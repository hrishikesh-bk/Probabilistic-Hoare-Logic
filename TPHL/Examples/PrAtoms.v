(** Deciding linear facts about formula probabilities.

    Given a list of atomic classical formulas (Boolean program variables and
    relations), every formula [g] built from them satisfies
      Pr(g) = sum over truth assignments L of the atoms that make g true
              of Pr(L),
    where [Pr(L)] is the probability of the conjunction of literals [L]
    ([Pr_atomize]).  Which assignments make [g] true is computed
    syntactically ([ceval]).  After rewriting every probability this way, a
    goal about formula probabilities becomes linear arithmetic over the
    nonnegative atom probabilities, whose total is at most 1, and [lra]
    finishes it.  The tactic is [patoms atoms]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Bool.
Require Import PHL.
Require Import Soundness.StateFacts Soundness.AssertionFacts.
Require Import Examples.Lib.

Open Scope R_scope.
Import ListNotations.

(** * Syntactic equality of formulas *)

Definition dvar_eqb (x y : DomProgramVar) : bool :=
  match x, y with dom_program_var s1, dom_program_var s2 => String.eqb s1 s2 end.
Definition bvar_eqb (x y : BoolProgramVar) : bool :=
  match x, y with bool_program_var s1, bool_program_var s2 => String.eqb s1 s2 end.
Definition dlvar_eqb (x y : DomLogicVar) : bool :=
  match x, y with dom_logic_var s1, dom_logic_var s2 => String.eqb s1 s2 end.
Definition blvar_eqb (x y : BoolLogicVar) : bool :=
  match x, y with bool_logic_var s1, bool_logic_var s2 => String.eqb s1 s2 end.

Definition op_eqb (o1 o2 : NatOp) : bool :=
  match o1, o2 with
  | NAdd, NAdd | NSub, NSub | NMul, NMul | NMod, NMod | NDiv, NDiv => true
  | _, _ => false
  end.
Definition rel_eqb (r1 r2 : NatRel) : bool :=
  match r1, r2 with
  | NLe, NLe | NEq, NEq | NLt, NLt => true
  | _, _ => false
  end.

Fixpoint term_eqb (t1 t2 : Term) : bool :=
  match t1, t2 with
  | TProgVar x, TProgVar y => dvar_eqb x y
  | TLogicVar x, TLogicVar y => dlvar_eqb x y
  | TConst c1, TConst c2 => Nat.eqb c1 c2
  | TOp o1 a1 b1, TOp o2 a2 b2 => op_eqb o1 o2 && term_eqb a1 a2 && term_eqb b1 b2
  | _, _ => false
  end.

Fixpoint cformula_eqb (g1 g2 : CFormula) : bool :=
  match g1, g2 with
  | FProgBool x, FProgBool y => bvar_eqb x y
  | FLogicBool x, FLogicBool y => blvar_eqb x y
  | FRel r1 a1 b1, FRel r2 a2 b2 => rel_eqb r1 r2 && term_eqb a1 a2 && term_eqb b1 b2
  | FFalse, FFalse => true
  | FImpl a1 b1, FImpl a2 b2 => cformula_eqb a1 a2 && cformula_eqb b1 b2
  | _, _ => false
  end.

Lemma term_eqb_sound t1 t2 : term_eqb t1 t2 = true -> t1 = t2.
Proof.
  revert t2; induction t1 as [x|x|c|o a IHa b IHb]; intros [y|y|c'|o' a' b']; cbn;
    try discriminate.
  - destruct x, y; intros H; apply String.eqb_eq in H; subst; reflexivity.
  - destruct x, y; intros H; apply String.eqb_eq in H; subst; reflexivity.
  - intros H; apply PeanoNat.Nat.eqb_eq in H; subst; reflexivity.
  - intros H; apply andb_prop in H as [H Hb]; apply andb_prop in H as [Ho Ha].
    destruct o, o'; try discriminate; rewrite (IHa _ Ha), (IHb _ Hb); reflexivity.
Qed.

Lemma cformula_eqb_sound g1 g2 : cformula_eqb g1 g2 = true -> g1 = g2.
Proof.
  revert g2; induction g1 as [x|x|r a b| |a IHa b IHb]; intros [y|y|r' a' b'| |a' b']; cbn;
    try discriminate.
  - destruct x, y; intros H; apply String.eqb_eq in H; subst; reflexivity.
  - destruct x, y; intros H; apply String.eqb_eq in H; subst; reflexivity.
  - intros H; apply andb_prop in H as [H Hb]; apply andb_prop in H as [Hr Ha].
    destruct r, r'; try discriminate;
      rewrite (term_eqb_sound _ _ Ha), (term_eqb_sound _ _ Hb); reflexivity.
  - reflexivity.
  - intros H; apply andb_prop in H as [Ha Hb].
    rewrite (IHa _ Ha), (IHb _ Hb); reflexivity.
Qed.

(** * Literals and assignments *)

Definition literal := (CFormula * bool)%type.

Definition lit_formula (l : literal) : CFormula :=
  if snd l then fst l else c_not (fst l).

Fixpoint conj_lits (L : list literal) : CFormula :=
  match L with
  | [] => c_true
  | l :: L' => c_and (lit_formula l) (conj_lits L')
  end.

Fixpoint assignments (atoms : list CFormula) : list (list literal) :=
  match atoms with
  | [] => [[]]
  | a :: atoms' =>
      map (cons (a, true)) (assignments atoms') ++ map (cons (a, false)) (assignments atoms')
  end.

Fixpoint lookup (L : list literal) (g : CFormula) : option bool :=
  match L with
  | [] => None
  | (a, p) :: L' => if cformula_eqb a g then Some p else lookup L' g
  end.

(** Truth value of [g] under the literals [L], when determined. *)
Fixpoint ceval (L : list literal) (g : CFormula) : option bool :=
  match g with
  | FFalse => Some false
  | FImpl a b =>
      match ceval L a, ceval L b with
      | Some false, _ => Some true
      | _, Some true => Some true
      | Some true, Some false => Some false
      | _, _ => None
      end
  | _ => lookup L g
  end.

Lemma satisfies_conj_lits v L :
  satisfies v (conj_lits L) <-> forall l, In l L -> satisfies v (lit_formula l).
Proof.
  induction L as [|l L IH]; cbn [conj_lits].
  - split; [intros _ l []|intros _; apply satisfies_true].
  - rewrite satisfies_and, IH. split.
    + intros [Hl HL] l' [<-|Hin]; auto.
    + intros H; split; [apply H; left; reflexivity | intros l' Hin; apply H; right; exact Hin].
Qed.

Lemma lookup_sound v L g p :
  lookup L g = Some p -> satisfies v (conj_lits L) -> (satisfies v g <-> p = true).
Proof.
  induction L as [|[a q] L IH]; cbn [lookup conj_lits]; [discriminate|].
  intros Hl Hsat. rewrite satisfies_and in Hsat. destruct Hsat as [Hq HL].
  destruct (cformula_eqb a g) eqn:E.
  - apply cformula_eqb_sound in E; subst a. injection Hl as <-.
    unfold lit_formula in Hq; cbn in Hq.
    destruct q; [tauto|]. rewrite satisfies_not in Hq. split; [tauto|discriminate].
  - exact (IH Hl HL).
Qed.

Lemma ceval_sound v L g p :
  ceval L g = Some p -> satisfies v (conj_lits L) -> (satisfies v g <-> p = true).
Proof.
  revert p; induction g as [x|x|r a b| |a IHa b IHb]; intros p.
  - apply lookup_sound.
  - apply lookup_sound.
  - apply lookup_sound.
  - cbn; intros H _; injection H as <-; split; [tauto|discriminate].
  - cbn [ceval]. intros H Hsat. cbn [satisfies].
    destruct (ceval L a) as [[|]|] eqn:Ea, (ceval L b) as [[|]|] eqn:Eb;
      injection H as <- || discriminate H;
      repeat match goal with
      | E : ceval L a = Some ?q |- _ => pose proof (IHa q eq_refl Hsat); clear E
      | E : ceval L b = Some ?q |- _ => pose proof (IHb q eq_refl Hsat); clear E
      end;
      intuition (try congruence; try discriminate).
Qed.

(** * Sums over assignments *)

Fixpoint rsum {A} (f : A -> R) (l : list A) : R :=
  match l with
  | [] => 0
  | x :: l' => f x + rsum f l'
  end.

Lemma rsum_app {A} (f : A -> R) l1 l2 : rsum f (l1 ++ l2) = rsum f l1 + rsum f l2.
Proof. induction l1; cbn; [lra|rewrite IHl1; lra]. Qed.

Lemma rsum_map {A B} (f : B -> R) (h : A -> B) l : rsum f (map h l) = rsum (fun x => f (h x)) l.
Proof. induction l; cbn; [reflexivity|rewrite IHl; reflexivity]. Qed.

Lemma rsum_ext {A} (f g : A -> R) l : (forall x, In x l -> f x = g x) -> rsum f l = rsum g l.
Proof.
  induction l as [|x l IH]; cbn; intros H; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|intros; apply H; right; assumption].
Qed.

Lemma rsum_nonneg {A} (f : A -> R) l : (forall x, 0 <= f x) -> 0 <= rsum f l.
Proof. intros H; induction l; cbn; [lra|pose proof (H a); lra]. Qed.

Section Atomize.
Variables (ps : Pstate) (Hps : pstate_admissible ps).

(** Probability of an assignment, kept folded so that tactics do not
    rewrite it again. *)
Definition Patom (L : list literal) : R := Pr[ps] (conj_lits L).
Definition Prest (L : list literal) (g : CFormula) : R := Pr[ps] (c_and (conj_lits L) g).

Lemma Pr_partition atoms g :
  Pr[ps] g = rsum (fun L => Pr[ps] (c_and (conj_lits L) g)) (assignments atoms).
Proof.
  revert g; induction atoms as [|a atoms IH]; intros g; cbn [assignments].
  - cbn [rsum]. rewrite Rplus_0_r. apply Pr_ext; intro v.
    cbn [conj_lits]. rewrite satisfies_and. pose proof (satisfies_true v); tauto.
  - rewrite rsum_app, !rsum_map.
    rewrite (Pr_split ps Hps g a), (IH (c_and g a)), (IH (c_and g (c_not a))).
    f_equal; apply rsum_ext; intros L _; apply Pr_ext; intro v;
      cbn [conj_lits lit_formula fst snd]; rewrite !satisfies_and; try rewrite !satisfies_not;
      tauto.
Qed.

Definition weight (L : list literal) (g : CFormula) : R :=
  match ceval L g with
  | Some true => Patom L
  | Some false => 0
  | None => Prest L g
  end.

Lemma weight_correct L g : Pr[ps] (c_and (conj_lits L) g) = weight L g.
Proof.
  unfold weight. destruct (ceval L g) as [[|]|] eqn:E.
  - unfold Patom. apply Pr_ext; intro v. rewrite satisfies_and.
    pose proof (fun Hs => ceval_sound v L g true E Hs). tauto.
  - rewrite <- (Pr_false ps). apply Pr_ext; intro v. rewrite satisfies_and.
    pose proof (fun Hs => ceval_sound v L g false E Hs). cbn [satisfies].
    split; [intros [Hs Hg]; apply H in Hs; apply Hs in Hg; discriminate | tauto].
  - reflexivity.
Qed.

Lemma Pr_atomize atoms g : Pr[ps] g = rsum (fun L => weight L g) (assignments atoms).
Proof.
  rewrite (Pr_partition atoms g). apply rsum_ext; intros L _; apply weight_correct.
Qed.

Lemma Patom_nonneg L : 0 <= Patom L.
Proof. apply Pr_nonneg. Qed.

Lemma Patom_total atoms : rsum Patom (assignments atoms) <= 1.
Proof.
  pose proof (Pr_true_le1 ps Hps) as H1.
  rewrite (Pr_partition atoms c_true) in H1.
  erewrite rsum_ext; [exact H1|]. intros L _. unfold Patom. apply Pr_ext; intro v.
  rewrite satisfies_and; pose proof (satisfies_true v); tauto.
Qed.

End Atomize.

(** * The tactic *)

Ltac patoms_compute :=
  cbn [rsum assignments map app weight ceval lookup cformula_eqb term_eqb bvar_eqb dvar_eqb
       dlvar_eqb blvar_eqb op_eqb rel_eqb String.eqb Ascii.eqb Bool.eqb andb Nat.eqb
       fst snd lit_formula c_and c_not c_or c_true c_iff c_le c_eq c_lt fvar tvar tnat
       t_add t_sub t_mul t_mod cbool] in *.

(** [patoms ps Hps atoms] rewrites every [Pr[ps] g] in the goal and the
    hypotheses over the assignments of [atoms], adds nonnegativity and total
    mass facts, and calls [lra]. *)
Ltac patoms_rewrite ps Hps atoms :=
  repeat match goal with
  | H : context [Pr[ps] ?g] |- _ =>
      rewrite (Pr_atomize ps Hps atoms g) in H
  | |- context [Pr[ps] ?g] =>
      rewrite (Pr_atomize ps Hps atoms g)
  end.

Ltac patoms_facts ps Hps atoms :=
  pose proof (Patom_total ps Hps atoms);
  repeat match goal with
  | |- context [Patom ps ?L] =>
      lazymatch goal with
      | _ : 0 <= Patom ps L |- _ => fail
      | _ => pose proof (Patom_nonneg ps L)
      end
  end.

Ltac split_hyps :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac patoms_with ps Hps atoms :=
  split_hyps;
  patoms_rewrite ps Hps atoms;
  patoms_facts ps Hps atoms;
  patoms_compute.

Tactic Notation "patoms" constr(atoms) :=
  match goal with
  | Hps : pstate_admissible ?ps |- _ => patoms_with ps Hps atoms
  end.

(** Full automation for a consequence side condition whose formulas are
    built from [atoms]. *)
(** Substitute atom probabilities fixed by a hypothesis [Patom L + 0 = r]. *)
Ltac patom_subst :=
  repeat match goal with
  | H : Patom ?ps ?L + 0 = ?r |- _ =>
      replace (Patom ps L) with r in * by lra; clear H
  | H : ?r = Patom ?ps ?L + 0 |- _ =>
      replace (Patom ps L) with r in * by lra; clear H
  end.

Ltac parith := first [lra | ring | (patom_subst; first [lra | ring | nra]) | nra].

Tactic Notation "pauto" constr(atoms) :=
  ptrans; pvalid; patoms atoms; try parith.
