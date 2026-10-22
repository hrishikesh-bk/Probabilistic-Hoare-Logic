(** Finite domains and classes of valuations (App. D).

    A finite domain enumerates its carrier and has an equality relation
    symbol, so that "x = c" is a classical formula.  For a finite list [V] of
    variables, the classes of [V] are the formulas [gamma_a] fixing the value
    of every variable in [V]; they partition the valuations.

    Unlike App. D, [V] contains the logic variables as well as the program
    variables: a class must decide every variable that the loop and the
    target formula [gamma] read, and [gamma] may mention logic variables. *)
From Stdlib Require Import List Bool Reals Lra Lia FunctionalExtensionality Permutation.
From mathcomp Require boolp.
Require Import PHL Soundness.StateFacts Soundness.LowerCertificate.
Import ListNotations.

Record FiniteDomain (D : Domain) : Type := {
  fd_enum : list D;
  fd_complete : forall c : D, In c fd_enum;
  fd_eq : dom_rel D;
  fd_eq_spec : forall a b, dom_rel_eval D fd_eq a b = true <-> a = b;
  fd_default : D
}.

Arguments fd_enum {D}.
Arguments fd_complete {D}.
Arguments fd_eq {D}.
Arguments fd_eq_spec {D}.
Arguments fd_default {D}.

(** ** A uniform view of the four kinds of classical variables *)

Inductive Var : Type :=
  | VDP (x : DomProgramVar)
  | VBP (b : BoolProgramVar)
  | VDL (x : DomLogicVar)
  | VBL (b : BoolLogicVar).

Definition var_eq_dec : forall u v : Var, {u = v} + {u <> v}.
Proof.
  decide equality;
    first [apply dom_program_var_eq_dec | apply bool_program_var_eq_dec
          | apply dom_logic_var_eq_dec | apply bool_logic_var_eq_dec].
Defined.

Section Vars.
Context {D : Domain}.

Inductive Val : Type :=
  | DVal (c : D)
  | BVal (b : bool).

Definition val_eq_dec : forall u v : Val, {u = v} + {u <> v}.
Proof. decide equality; [apply dom_eq_dec | apply bool_dec]. Defined.

Definition read (w : state D) (v : Var) : Val :=
  match v with
  | VDP x => DVal (dom_program_values w x)
  | VBP b => BVal (bool_program_values w b)
  | VDL x => DVal (dom_logic_values w x)
  | VBL b => BVal (bool_logic_values w b)
  end.

Definition agree (V : list Var) (w w' : state D) : Prop :=
  forall v, In v V -> read w v = read w' v.

Lemma agree_sym V w w' : agree V w w' -> agree V w' w.
Proof. intros H v Hv; symmetry; apply H; exact Hv. Qed.

Lemma agree_trans V w1 w2 w3 : agree V w1 w2 -> agree V w2 w3 -> agree V w1 w3.
Proof. intros H1 H2 v Hv; rewrite H1, H2 by exact Hv; reflexivity. Qed.

Lemma agree_incl V V' w w' : incl V V' -> agree V' w w' -> agree V w w'.
Proof. intros Hi H v Hv; apply H, Hi, Hv. Qed.

(** ** Variables of syntax *)

Fixpoint term_vars (t : Term D) : list Var :=
  match t with
  | TProgVar x => [VDP x]
  | TLogicVar x => [VDL x]
  | TConst _ => []
  | TOp _ t1 t2 => term_vars t1 ++ term_vars t2
  end.

Fixpoint cformula_vars (g : CFormula D) : list Var :=
  match g with
  | FProgBool b => [VBP b]
  | FLogicBool b => [VBL b]
  | FRel _ t1 t2 => term_vars t1 ++ term_vars t2
  | FFalse => []
  | FImpl g1 g2 => cformula_vars g1 ++ cformula_vars g2
  end.

Fixpoint cmd_vars (c : Cmd D) : list Var :=
  match c with
  | CSkip => []
  | CDomAssign x t => VDP x :: term_vars t
  | CBoolAssign b beta => VBP b :: cformula_vars beta
  | CBoolToss b _ => [VBP b]
  | CSeq c1 c2 => cmd_vars c1 ++ cmd_vars c2
  | CIf beta c1 c2 => cformula_vars beta ++ cmd_vars c1 ++ cmd_vars c2
  | CWhile beta body => cformula_vars beta ++ cmd_vars body
  end.

Lemma term_eval_agree V t w w' :
  incl (term_vars t) V -> agree V w w' -> term_eval t w = term_eval t w'.
Proof.
  intros Hi H. induction t as [x|x|c|o t1 IH1 t2 IH2]; cbn in *.
  - specialize (H (VDP x) (Hi _ (or_introl eq_refl))). cbn in H. congruence.
  - specialize (H (VDL x) (Hi _ (or_introl eq_refl))). cbn in H. congruence.
  - reflexivity.
  - rewrite IH1, IH2; [reflexivity | |];
      intros v Hv; apply Hi, in_app_iff; auto.
Qed.

Lemma satisfies_agree V g w w' :
  incl (cformula_vars g) V -> agree V w w' -> (satisfies w g <-> satisfies w' g).
Proof.
  intros Hi H. induction g as [b|b|r t1 t2| |g1 IH1 g2 IH2]; cbn in *.
  - specialize (H (VBP b) (Hi _ (or_introl eq_refl))). cbn in H. inversion H. reflexivity.
  - specialize (H (VBL b) (Hi _ (or_introl eq_refl))). cbn in H. inversion H. reflexivity.
  - rewrite (term_eval_agree V t1 w w'), (term_eval_agree V t2 w w');
      [reflexivity | | | |]; try exact H; intros v Hv; apply Hi, in_app_iff; auto.
  - reflexivity.
  - rewrite IH1, IH2; [reflexivity | |]; intros v Hv; apply Hi, in_app_iff; auto.
Qed.

Lemma eval_bool_agree V g w w' :
  incl (cformula_vars g) V -> agree V w w' ->
  cformula_eval_bool g w = cformula_eval_bool g w'.
Proof.
  intros Hi H.
  destruct (cformula_eval_bool g w) eqn:E1, (cformula_eval_bool g w') eqn:E2; auto.
  - apply cformula_eval_bool_spec in E1. apply cformula_eval_bool_false in E2.
    exfalso; apply E2; apply (satisfies_agree V g w w' Hi H); exact E1.
  - apply cformula_eval_bool_false in E1. apply cformula_eval_bool_spec in E2.
    exfalso; apply E1; apply (satisfies_agree V g w w' Hi H); exact E2.
Qed.

(** Updating both valuations identically preserves agreement. *)
Lemma agree_update_dom V w w' x c :
  agree V w w' -> agree V (update_dom w x c) (update_dom w' x c).
Proof.
  intros H v Hv. specialize (H v Hv). destruct v; cbn in *; try exact H.
  destruct (dom_program_var_eq_dec x0 x); [reflexivity | exact H].
Qed.

Lemma agree_update_bool V w w' b z :
  agree V w w' -> agree V (update_bool w b z) (update_bool w' b z).
Proof.
  intros H v Hv. specialize (H v Hv). destruct v; cbn in *; try exact H.
  destruct (bool_program_var_eq_dec b0 b); [reflexivity | exact H].
Qed.

End Vars.

Arguments Val : clear implicits.

(** ** Classes *)

Section Classes.
Context {D : Domain} (FD : FiniteDomain D).

Definition values_of (v : Var) : list (Val D) :=
  match v with
  | VDP _ | VDL _ => map DVal (fd_enum FD)
  | VBP _ | VBL _ => [BVal true; BVal false]
  end.

Lemma read_in_values w v : In (read w v) (values_of v).
Proof.
  destruct v as [x|b|x|b]; cbn.
  - apply in_map, fd_complete.
  - destruct (bool_program_values w b); cbn; auto.
  - apply in_map, fd_complete.
  - destruct (bool_logic_values w b); cbn; auto.
Qed.

Definition Assignment : Type := list (Var * Val D).

Fixpoint assignments (V : list Var) : list Assignment :=
  match V with
  | [] => [[]]
  | v :: V' => flat_map (fun a => map (fun c => (v, c) :: a) (values_of v)) (assignments V')
  end.

Definition assignment_of (V : list Var) (w : state D) : Assignment :=
  map (fun v => (v, read w v)) V.

Lemma assignment_of_in V w : In (assignment_of V w) (assignments V).
Proof.
  induction V as [|v V IH]; cbn [assignments]; [left; reflexivity|].
  change (assignment_of (v :: V) w) with ((v, read w v) :: assignment_of V w).
  apply in_flat_map. exists (assignment_of V w). split; [exact IH|].
  apply (in_map (fun c => (v, c) :: assignment_of V w)). apply read_in_values.
Qed.

Lemma assignments_keys V a : In a (assignments V) -> map fst a = V.
Proof.
  revert a; induction V as [|v V IH]; intros a Ha; cbn in Ha.
  - destruct Ha as [<-|[]]; reflexivity.
  - apply in_flat_map in Ha. destruct Ha as [a' [Ha' Hin]].
    apply in_map_iff in Hin. destruct Hin as [c [<- _]]. cbn. f_equal. apply IH, Ha'.
Qed.

Definition literal (p : Var * Val D) : CFormula D :=
  match p with
  | (VDP x, DVal c) => FRel (fd_eq FD) (TProgVar x) (TConst c)
  | (VDL x, DVal c) => FRel (fd_eq FD) (TLogicVar x) (TConst c)
  | (VBP b, BVal true) => FProgBool b
  | (VBP b, BVal false) => c_not (FProgBool b)
  | (VBL b, BVal true) => FLogicBool b
  | (VBL b, BVal false) => c_not (FLogicBool b)
  | _ => FFalse
  end.

Lemma satisfies_literal w p : satisfies w (literal p) <-> read w (fst p) = snd p.
Proof.
  destruct p as [[x|b|x|b] [c|z]]; cbn.
  - rewrite (fd_eq_spec FD). split; [intros ->; reflexivity | intros H; inversion H; reflexivity].
  - split; [contradiction | discriminate].
  - split; [contradiction | discriminate].
  - destruct z; cbn; split; intros H.
    + rewrite H; reflexivity.
    + inversion H; reflexivity.
    + destruct (bool_program_values w b); [contradiction H; reflexivity | reflexivity].
    + inversion H as [H']. rewrite H'. discriminate.
  - rewrite (fd_eq_spec FD). split; [intros ->; reflexivity | intros H; inversion H; reflexivity].
  - split; [contradiction | discriminate].
  - split; [contradiction | discriminate].
  - destruct z; cbn; split; intros H.
    + rewrite H; reflexivity.
    + inversion H; reflexivity.
    + destruct (bool_logic_values w b); [contradiction H; reflexivity | reflexivity].
    + inversion H as [H']. rewrite H'. discriminate.
Qed.

Definition class_formula (a : Assignment) : CFormula D :=
  fold_right (fun p acc => c_and (literal p) acc) c_true a.

Lemma satisfies_class w a :
  satisfies w (class_formula a) <-> forall p, In p a -> read w (fst p) = snd p.
Proof.
  induction a as [|p a IH]; cbn [class_formula fold_right].
  - split; [intros _ p [] | intros _; apply satisfies_true].
  - rewrite satisfies_and, satisfies_literal, IH. cbn. split.
    + intros [H1 H2] q [<-|Hq]; auto.
    + intros H; split; auto.
Qed.

Lemma satisfies_own_class V w : satisfies w (class_formula (assignment_of V w)).
Proof.
  apply satisfies_class. intros p Hp. unfold assignment_of in Hp.
  apply in_map_iff in Hp. destruct Hp as [v [<- _]]. reflexivity.
Qed.

(** A valuation in a class is the class's own assignment. *)
Lemma class_unique a w :
  satisfies w (class_formula a) -> a = assignment_of (map fst a) w.
Proof.
  intros Hw0; pose proof (proj1 (satisfies_class w a) Hw0) as Hw; clear Hw0.
  unfold assignment_of; rewrite map_map.
  induction a as [|[v c] a IH]; cbn; [reflexivity|].
  f_equal.
  - f_equal. symmetry. exact (Hw (v,c) (or_introl eq_refl)).
  - apply IH. intros p Hp; apply Hw; right; exact Hp.
Qed.

Lemma literal_vars p : incl (cformula_vars (literal p)) [fst p].
Proof.
  destruct p as [[x|b|x|b] [c|z]]; try destruct z; intros u Hu;
    simpl in Hu |- *; rewrite ?app_nil_r in Hu; simpl in Hu;
    try contradiction; destruct Hu as [Hu|Hu]; try contradiction; subst; auto.
Qed.

Lemma class_vars_incl a : incl (cformula_vars (class_formula a)) (map fst a).
Proof.
  induction a as [|p a IH]; cbn [class_formula fold_right]; intros u Hu.
  - cbn in Hu; contradiction.
  - unfold c_and, c_not in Hu. cbn [cformula_vars] in Hu.
    rewrite ?app_nil_r, ?in_app_iff in Hu. cbn [map].
    destruct Hu as [Hl | Hr].
    + apply literal_vars in Hl. destruct Hl as [<- | []]. left; reflexivity.
    + right; apply IH, Hr.
Qed.

Lemma class_agree a w w' :
  satisfies w (class_formula a) -> satisfies w' (class_formula a) ->
  agree (map fst a) w w'.
Proof.
  intros H H' v Hv. apply in_map_iff in Hv. destruct Hv as [[u c] [<- Hin]]. cbn.
  pose proof (proj1 (satisfies_class w a) H (u,c) Hin) as E1.
  pose proof (proj1 (satisfies_class w' a) H' (u,c) Hin) as E2.
  cbn in E1, E2. congruence.
Qed.

Definition assignment_eq_dec : forall a b : Assignment, {a = b} + {a <> b}.
Proof.
  apply list_eq_dec. intros [u c] [v d].
  destruct (var_eq_dec u v), (val_eq_dec c d); subst; [left; reflexivity | right; congruence ..].
Defined.

Definition class_nonempty (a : Assignment) : Prop :=
  exists w : state D, satisfies w (class_formula a).

(** The nonempty classes of [V], without duplicates. *)
Definition classes (V : list Var) : list Assignment :=
  filter (fun a => if boolp.pselect (class_nonempty a) then true else false)
    (nodup assignment_eq_dec (assignments V)).

Lemma classes_nodup V : NoDup (classes V).
Proof. apply NoDup_filter, NoDup_nodup. Qed.

Lemma classes_spec V a :
  In a (classes V) <-> In a (assignments V) /\ class_nonempty a.
Proof.
  unfold classes. rewrite filter_In, nodup_In.
  destruct (boolp.pselect (class_nonempty a)); intuition discriminate.
Qed.

Lemma classes_keys V a : In a (classes V) -> map fst a = V.
Proof. intros H; apply classes_spec in H; apply assignments_keys, H. Qed.

Lemma classes_own V w : In (assignment_of V w) (classes V).
Proof.
  apply classes_spec; split; [apply assignment_of_in |].
  exists w; apply satisfies_own_class.
Qed.

Lemma classes_member V a w :
  In a (classes V) -> satisfies w (class_formula a) -> a = assignment_of V w.
Proof.
  intros Ha Hw. rewrite (class_unique a w Hw). f_equal. apply classes_keys, Ha.
Qed.

Lemma classes_disjoint V a a' w :
  In a (classes V) -> In a' (classes V) ->
  satisfies w (class_formula a) -> satisfies w (class_formula a') -> a = a'.
Proof.
  intros Ha Ha' Hw Hw'. rewrite (classes_member V a w Ha Hw), (classes_member V a' w Ha' Hw').
  reflexivity.
Qed.

Lemma classes_agree V a w w' :
  In a (classes V) -> satisfies w (class_formula a) -> satisfies w' (class_formula a) ->
  agree V w w'.
Proof.
  intros Ha H H'. rewrite <- (classes_keys V a Ha). apply class_agree; assumption.
Qed.

Lemma class_formula_vars_classes V a :
  In a (classes V) -> incl (cformula_vars (class_formula a)) V.
Proof. intros Ha. rewrite <- (classes_keys V a Ha). apply class_vars_incl. Qed.

(** Some valuation exists, so some class is nonempty. *)
Definition default_valuation : state D :=
  {| dom_program_values := fun _ => fd_default FD;
     bool_program_values := fun _ => true;
     dom_logic_values := fun _ => fd_default FD;
     bool_logic_values := fun _ => true |}.

Lemma classes_nonnil V : classes V <> [].
Proof.
  intros H. pose proof (classes_own V default_valuation) as Hin. rewrite H in Hin. exact Hin.
Qed.

End Classes.

(** ** Finite sums of reals over lists *)

Section RealListSums.
Context {X : Type}.
Local Open Scope R_scope.

Fixpoint rsum (l : list X) (f : X -> R) : R :=
  match l with
  | [] => 0
  | x :: l' => f x + rsum l' f
  end.

Lemma rsum_app l1 l2 f : rsum (l1 ++ l2) f = rsum l1 f + rsum l2 f.
Proof. induction l1; cbn; lra. Qed.

Lemma rsum_ext l f g : (forall x, In x l -> f x = g x) -> rsum l f = rsum l g.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite H, IH; [reflexivity | intros; apply H; right; assumption | left; reflexivity].
Qed.

Lemma rsum_zero l f : (forall x, In x l -> f x = 0) -> rsum l f = 0.
Proof.
  intros H. rewrite (rsum_ext l f (fun _ => 0)) by exact H.
  clear H. induction l; cbn; lra.
Qed.

Lemma rsum_perm l1 l2 f : Permutation l1 l2 -> rsum l1 f = rsum l2 f.
Proof. induction 1; cbn; lra. Qed.

Lemma rsum_filter (p : X -> bool) l f :
  rsum l f = rsum (filter p l) f + rsum (filter (fun x => negb (p x)) l) f.
Proof. induction l as [|x l IH]; cbn; [lra|]. destruct (p x); cbn; lra. Qed.

Lemma rsum_nonneg l f : (forall x, In x l -> 0 <= f x) -> 0 <= rsum l f.
Proof.
  induction l as [|x l IH]; intros H; cbn; [lra|].
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y hy => H y (or_intror hy))). lra.
Qed.

Lemma rsum_le l f g : (forall x, In x l -> f x <= g x) -> rsum l f <= rsum l g.
Proof.
  induction l as [|x l IH]; intros H; cbn; [lra|].
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y hy => H y (or_intror hy))). lra.
Qed.

Lemma rsum_pos_term l f : (forall x, In x l -> 0 <= f x) -> 0 < rsum l f ->
  exists x, In x l /\ 0 < f x.
Proof.
  induction l as [|x l IH]; intros H Hp; cbn in Hp; [lra|].
  destruct (Rlt_le_dec 0 (f x)) as [h|h]; [exists x; split; [left|]; auto|].
  destruct (IH (fun y hy => H y (or_intror hy))) as [y [hy hy']]; [lra|].
  exists y; split; [right|]; assumption.
Qed.

Lemma finite_r_sum_nth l (f : X -> R) d :
  finite_r_sum (length l) (fun j => f (nth j l d)) = rsum l f.
Proof.
  induction l as [|x l IH] using rev_ind; [reflexivity|].
  rewrite length_app, Nat.add_comm. change (length [x]) with 1%nat. cbn [Nat.add finite_r_sum].
  rewrite rsum_app. cbn [rsum]. cbv beta.
  rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
  rewrite (finite_r_sum_ext (length l) (fun j => f (nth j (l ++ [x]) d))
             (fun j => f (nth j l d))).
  - rewrite IH. lra.
  - intros j hj. rewrite app_nth1 by exact hj. reflexivity.
Qed.

End RealListSums.
