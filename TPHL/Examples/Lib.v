(** Shared library for the example derivations.

    The examples are written over [nat_domain].  This file provides
    - notations for programs ([<{ c }>]), classical formulas ([\{ f \}]) and
      probabilistic formulas ([{{ eta }}]);
    - facts about formula probabilities [Pr[ps] gamma];
    - tactics that turn a consequence side condition into arithmetic over
      formula probabilities;
    - derived rules: consequence on one side, exact IF, and instantiating a
      probabilistic logic variable by a constant. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
From Stdlib Require Import Setoid.
Require Import PHL.
Require Import Soundness.StateFacts Soundness.AssertionFacts.
Require Import Completeness.StructuralRules.

Open Scope R_scope.
Open Scope string_scope.

(** * Specialization to [nat_domain] *)

Notation Term := (PHL.Term nat_domain).
Notation CFormula := (PHL.CFormula nat_domain).
Notation Cmd := (PHL.Cmd nat_domain).
Notation Pterm := (PHL.Pterm nat_domain).
Notation PFormula := (PHL.PFormula nat_domain).
Notation Pstate := (PHL.Pstate nat_domain).
Notation state := (PHL.state nat_domain).

Definition tnat (n : nat) : Term := TConst (D := nat_domain) n.

Definition t_add (t1 t2 : Term) : Term := TOp (D := nat_domain) NAdd t1 t2.
Definition t_sub (t1 t2 : Term) : Term := TOp (D := nat_domain) NSub t1 t2.
Definition t_mul (t1 t2 : Term) : Term := TOp (D := nat_domain) NMul t1 t2.
Definition t_mod (t1 t2 : Term) : Term := TOp (D := nat_domain) NMod t1 t2.
Definition t_div (t1 t2 : Term) : Term := TOp (D := nat_domain) NDiv t1 t2.

Lemma term_eval_div t1 t2 v :
  term_eval (t_div t1 t2) v = Nat.div (term_eval t1 v) (term_eval t2 v).
Proof. reflexivity. Qed.

Definition c_le (t1 t2 : Term) : CFormula := FRel (D := nat_domain) NLe t1 t2.
Definition c_eq (t1 t2 : Term) : CFormula := FRel (D := nat_domain) NEq t1 t2.
Definition c_lt (t1 t2 : Term) : CFormula := FRel (D := nat_domain) NLt t1 t2.

Definition p_ge (p1 p2 : Pterm) : PFormula := PFLe p2 p1.

(** Coercions so that variables and constants can be written directly. *)
Definition tvar (x : DomProgramVar) : Term := TProgVar x.
Definition fvar (b : BoolProgramVar) : CFormula := FProgBool b.
Definition pvar (y : ProbLogicVar) : Pterm := PVar y.
Definition pconst (r : R) : Pterm := PConst r.
Coercion tnat : nat >-> Term.
Coercion tvar : DomProgramVar >-> Term.
Coercion fvar : BoolProgramVar >-> CFormula.
Coercion pvar : ProbLogicVar >-> Pterm.
Coercion pconst : R >-> Pterm.

(** A Coq Boolean as a constant formula. *)
Definition cbool (k : bool) : CFormula := if k then c_true else FFalse.
Coercion cbool : bool >-> CFormula.

(** * Notations *)

Declare Custom Entry tcom.
Declare Custom Entry tcf.
Declare Custom Entry tpf.
Declare Scope tphl_scope.
Delimit Scope tphl_scope with tphl.
Open Scope tphl_scope.

(** Classical formulas and terms. *)
Notation "\{ f \}" := f (f custom tcf at level 99) : tphl_scope.
Notation "( x )" := x (in custom tcf at level 0, x at level 99) : tphl_scope.
Notation "x" := x (in custom tcf at level 0, x constr at level 0) : tphl_scope.
Notation "'#(' x ')'" := x (in custom tcf at level 0, x constr at level 200) : tphl_scope.
Notation "'true'" := (c_true (D := nat_domain)) (in custom tcf at level 0) : tphl_scope.
Notation "'false'" := (FFalse (D := nat_domain)) (in custom tcf at level 0) : tphl_scope.
Notation "x + y" := (t_add x y) (in custom tcf at level 50, left associativity) : tphl_scope.
Notation "x - y" := (t_sub x y) (in custom tcf at level 50, left associativity) : tphl_scope.
Notation "x * y" := (t_mul x y) (in custom tcf at level 40, left associativity) : tphl_scope.
Notation "x 'mod' y" := (t_mod x y) (in custom tcf at level 40, left associativity) : tphl_scope.
Notation "x 'div' y" := (t_div x y) (in custom tcf at level 40, left associativity) : tphl_scope.
Notation "x <= y" := (c_le x y) (in custom tcf at level 60, no associativity) : tphl_scope.
Notation "x < y" := (c_lt x y) (in custom tcf at level 60, no associativity) : tphl_scope.
Notation "x = y" := (c_eq x y) (in custom tcf at level 60, no associativity) : tphl_scope.
Notation "'~' x" := (c_not x) (in custom tcf at level 70, right associativity) : tphl_scope.
Notation "x /\ y" := (c_and x y) (in custom tcf at level 80, right associativity) : tphl_scope.
Notation "x \/ y" := (c_or x y) (in custom tcf at level 85, right associativity) : tphl_scope.
Notation "x -> y" := (FImpl x y) (in custom tcf at level 90, right associativity) : tphl_scope.
Notation "x <-> y" := (c_iff x y) (in custom tcf at level 95, no associativity) : tphl_scope.

(** Probabilistic formulas. *)
Notation "{{ e }}" := e (e custom tpf at level 99) : tphl_scope.
Notation "( x )" := x (in custom tpf at level 0, x at level 99) : tphl_scope.
Notation "x" := x (in custom tpf at level 0, x constr at level 0) : tphl_scope.
Notation "'prob' g" := (PProb g) (in custom tpf at level 1, g custom tcf at level 0) : tphl_scope.
Notation "'true'" := (p_true (D := nat_domain)) (in custom tpf at level 0) : tphl_scope.
Notation "'false'" := (PFFalse (D := nat_domain)) (in custom tpf at level 0) : tphl_scope.
Notation "x + y" := (PAdd x y) (in custom tpf at level 50, left associativity) : tphl_scope.
Notation "x * y" := (PMul x y) (in custom tpf at level 40, left associativity) : tphl_scope.
Notation "x <= y" := (PFLe x y) (in custom tpf at level 60, no associativity) : tphl_scope.
Notation "x >= y" := (p_ge x y) (in custom tpf at level 60, no associativity) : tphl_scope.
Notation "x = y" := (p_eq x y) (in custom tpf at level 60, no associativity) : tphl_scope.
Notation "'box' g" := (p_almost_sure g) (in custom tpf at level 1, g custom tcf at level 0) : tphl_scope.
Notation "'~' x" := (p_not x) (in custom tpf at level 70, right associativity) : tphl_scope.
Notation "x /\ y" := (p_and x y) (in custom tpf at level 80, right associativity) : tphl_scope.
Notation "x \/ y" := (p_or x y) (in custom tpf at level 85, right associativity) : tphl_scope.
Notation "x -> y" := (PFImpl x y) (in custom tpf at level 90, right associativity) : tphl_scope.

(** Programs. *)
Notation "<{ c }>" := c (c custom tcom at level 99) : tphl_scope.
Notation "( x )" := x (in custom tcom at level 0, x at level 99) : tphl_scope.
Notation "x" := x (in custom tcom at level 0, x constr at level 0) : tphl_scope.
Notation "'skip'" := (CSkip (D := nat_domain)) (in custom tcom at level 0) : tphl_scope.
Notation "x := t" := (CDomAssign x t)
  (in custom tcom at level 0, x constr at level 0, t custom tcf at level 85,
   no associativity) : tphl_scope.
Notation "b 'b=' f" := (CBoolAssign b f)
  (in custom tcom at level 0, b constr at level 0, f custom tcf at level 85,
   no associativity) : tphl_scope.
Notation "b 'toss' r" := (CBoolToss (D := nat_domain) b r)
  (in custom tcom at level 0, b constr at level 0, r constr at level 0,
   no associativity) : tphl_scope.
Notation "x ; y" := (CSeq x y) (in custom tcom at level 90, right associativity) : tphl_scope.
Notation "'if' g 'then' x 'else' y 'end'" := (CIf g x y)
  (in custom tcom at level 89, g custom tcf at level 99, x at level 99, y at level 99)
  : tphl_scope.
Notation "'while' g 'do' x 'end'" := (CWhile g x)
  (in custom tcom at level 89, g custom tcf at level 99, x at level 99) : tphl_scope.

(** * Probabilities of formulas *)

Notation "'Pr[' ps ']' g" := (measure_of (pstate_measure ps) (formula_assertion g))
  (at level 10, ps at level 0, g at level 0).

Section Probabilities.
Implicit Types (ps : Pstate) (g h : CFormula).

Lemma Pr_ext ps g h :
  (forall v, satisfies v g <-> satisfies v h) -> Pr[ps] g = Pr[ps] h.
Proof. intros H; rewrite (formula_assertion_ext g h H); reflexivity. Qed.

Lemma Pr_nonneg ps g : 0 <= Pr[ps] g.
Proof. apply measure_nonnegative. Qed.

Lemma Pr_false ps : Pr[ps] FFalse = 0.
Proof.
  rewrite <- (measure_empty (pstate_measure ps)).
  apply measure_extensional; intro v; cbn; tauto.
Qed.

Section Admissible.
Variables (ps : Pstate) (Hps : pstate_admissible ps).

Lemma Pr_disjoint g h :
  (forall v, ~ (satisfies v g /\ satisfies v h)) ->
  Pr[ps] (c_or g h) = Pr[ps] g + Pr[ps] h.
Proof.
  intros Hd. unfold formula_assertion.
  rewrite <- measure_additive.
  - apply measure_extensional; intro v. rewrite satisfies_or. tauto.
  - exact (MeasureIntegration.ConcreteMeasure.subprob_finite Hps).
  - exact Hd.
Qed.

(** [Pr(g) = Pr(g /\ h) + Pr(g /\ ~h)]. *)
Lemma Pr_split g h : Pr[ps] g = Pr[ps] (c_and g h) + Pr[ps] (c_and g (c_not h)).
Proof.
  rewrite <- Pr_disjoint.
  - apply Pr_ext; intro v. rewrite satisfies_or, !satisfies_and, satisfies_not.
    destruct (satisfies_dec v h); tauto.
  - intros v. rewrite !satisfies_and, satisfies_not. tauto.
Qed.

Lemma Pr_mono g h : (forall v, satisfies v g -> satisfies v h) -> Pr[ps] g <= Pr[ps] h.
Proof.
  intros Himp. rewrite (Pr_split h g).
  replace (Pr[ps] (c_and h g)) with (Pr[ps] g).
  - pose proof (Pr_nonneg ps (c_and h (c_not g))); lra.
  - apply Pr_ext; intro v; rewrite satisfies_and; split; [intros Hg; split; auto | tauto].
Qed.

Lemma Pr_le_true g : Pr[ps] g <= Pr[ps] c_true.
Proof. apply Pr_mono; intros v _; apply satisfies_true. Qed.

Lemma Pr_true_le1 : Pr[ps] c_true <= 1.
Proof.
  rewrite formula_assertion_true. exact (measure_subprobability _ Hps).
Qed.

End Admissible.
End Probabilities.

(** * Deciding classical equivalences

    [cdecide] proves goals [satisfies v g <-> satisfies v h] (and
    implications) for concrete formulas by unfolding the connectives and
    case analysis on every Boolean program variable and numeric relation that
    occurs. *)

Ltac cunfold :=
  unfold c_and, c_or, c_not, c_true, c_iff, c_le, c_eq, c_lt, fvar, tvar, tnat,
         t_add, t_sub, t_mul, t_mod in *;
  cbn [satisfies term_eval dom_rel_eval dom_op_eval nat_domain nat_rel_eval nat_op_eval
       subst_bool_cformula subst_dom_cformula subst_dom_term] in *.

Ltac cdestruct :=
  repeat match goal with
  | |- context [bool_program_values ?v ?b] =>
      let e := fresh "e" in destruct (bool_program_values v b) eqn:e
  | |- context [Nat.eqb ?a ?c] =>
      let e := fresh "e" in destruct (Nat.eqb a c) eqn:e
  | |- context [Nat.leb ?a ?c] =>
      let e := fresh "e" in destruct (Nat.leb a c) eqn:e
  | |- context [Nat.ltb ?a ?c] =>
      let e := fresh "e" in destruct (Nat.ltb a c) eqn:e
  end.

Ltac cdecide :=
  let v := fresh "v" in
  try (intros v);
  cunfold;
  cdestruct;
  try (intuition congruence);
  try (rewrite ?Nat.eqb_eq, ?Nat.eqb_neq, ?Nat.leb_le, ?Nat.leb_gt, ?Nat.ltb_lt, ?Nat.ltb_ge in *;
       intuition (try congruence; try lia)).

(** [pr_eq] rewrites [Pr[ps] g] into [Pr[ps] h] when [g] and [h] are
    equivalent. *)
Ltac pr_eq g h :=
  let E := fresh "E" in
  assert (E : forall ps, Pr[ps] g = Pr[ps] h) by (intros; apply Pr_ext; cdecide);
  rewrite ?E in *; clear E.

(** * Consequence side conditions

    [pvalid] opens a goal [pformula_valid (PFImpl eta1 eta2)], computes the
    syntactic transformers (substitution, tossed and conditioned formulas)
    and turns the connectives into Coq connectives over [Pr[ps] _]. *)

Lemma psatisfies_true_iff (ps : Pstate) : psatisfies ps p_true <-> True.
Proof. split; [tauto|intros _; apply psatisfies_true]. Qed.

Ltac psimpl_in H :=
  repeat first
    [ rewrite psatisfies_and in H
    | rewrite psatisfies_or in H
    | rewrite psatisfies_not in H
    | rewrite psatisfies_eq in H
    | rewrite psatisfies_almost_sure in H
    | rewrite psatisfies_impl in H
    | rewrite psatisfies_le in H
    | rewrite psatisfies_true_iff in H
    | unfold p_ge, p_concentrated_unit, if_precondition, sum_precondition in H ].

Ltac psimpl_goal :=
  repeat first
    [ rewrite psatisfies_and
    | rewrite psatisfies_or
    | rewrite psatisfies_not
    | rewrite psatisfies_eq
    | rewrite psatisfies_almost_sure
    | rewrite psatisfies_impl
    | rewrite psatisfies_le
    | rewrite psatisfies_true_iff
    | unfold p_ge, p_concentrated_unit, if_precondition, sum_precondition ].

(** The syntactic transformers commute with the derived connectives
    (definitionally, since those are built from [PFImpl] and [PFFalse]). *)
Section Commute.
Variable T : PFormula -> PFormula.
Hypothesis T_impl : forall e1 e2, T (PFImpl e1 e2) = PFImpl (T e1) (T e2).
Hypothesis T_false : T PFFalse = PFFalse.

Lemma T_not e : T (p_not e) = p_not (T e).
Proof. unfold p_not; rewrite T_impl, T_false; reflexivity. Qed.
Lemma T_and e1 e2 : T (p_and e1 e2) = p_and (T e1) (T e2).
Proof. unfold p_and; rewrite T_not, T_impl, T_not; reflexivity. Qed.
Lemma T_or e1 e2 : T (p_or e1 e2) = p_or (T e1) (T e2).
Proof. unfold p_or; rewrite T_impl, T_not; reflexivity. Qed.
Lemma T_true : T p_true = p_true.
Proof. unfold p_true; rewrite T_impl, T_false; reflexivity. Qed.
End Commute.

Section CommuteLe.
Variable T : PFormula -> PFormula.
Variable Tp : Pterm -> Pterm.
Hypothesis T_le : forall p1 p2, T (PFLe p1 p2) = PFLe (Tp p1) (Tp p2).
Hypothesis T_impl : forall e1 e2, T (PFImpl e1 e2) = PFImpl (T e1) (T e2).
Hypothesis T_false : T PFFalse = PFFalse.

Lemma T_eq p1 p2 : T (p_eq p1 p2) = p_eq (Tp p1) (Tp p2).
Proof. unfold p_eq; rewrite (T_and T T_impl T_false), !T_le; reflexivity. Qed.
Lemma T_ge p1 p2 : T (p_ge p1 p2) = p_ge (Tp p1) (Tp p2).
Proof. unfold p_ge; apply T_le. Qed.
End CommuteLe.

Section CommuteCondition.
Variable g : CFormula.
Lemma cond_impl e1 e2 :
  condition_pformula (PFImpl e1 e2) g = PFImpl (condition_pformula e1 g) (condition_pformula e2 g).
Proof. reflexivity. Qed.
Lemma cond_le p1 p2 :
  condition_pformula (PFLe p1 p2) g = PFLe (condition_pterm p1 g) (condition_pterm p2 g).
Proof. reflexivity. Qed.
Lemma cond_not e : condition_pformula (p_not e) g = p_not (condition_pformula e g).
Proof. reflexivity. Qed.
Lemma cond_and e1 e2 :
  condition_pformula (p_and e1 e2) g = p_and (condition_pformula e1 g) (condition_pformula e2 g).
Proof. reflexivity. Qed.
Lemma cond_or e1 e2 :
  condition_pformula (p_or e1 e2) g = p_or (condition_pformula e1 g) (condition_pformula e2 g).
Proof. reflexivity. Qed.
Lemma cond_true : condition_pformula p_true g = p_true.
Proof. reflexivity. Qed.
Lemma cond_eq p1 p2 :
  condition_pformula (p_eq p1 p2) g = p_eq (condition_pterm p1 g) (condition_pterm p2 g).
Proof. reflexivity. Qed.
Lemma cond_ge p1 p2 :
  condition_pformula (p_ge p1 p2) g = p_ge (condition_pterm p1 g) (condition_pterm p2 g).
Proof. reflexivity. Qed.
End CommuteCondition.

Ltac commute_one T Tp :=
  let Hi := fresh in let Hf := fresh in let Hl := fresh in
  assert (Hi : forall e1 e2, T (PFImpl e1 e2) = PFImpl (T e1) (T e2)) by reflexivity;
  assert (Hf : T PFFalse = PFFalse) by reflexivity;
  assert (Hl : forall p1 p2, T (PFLe p1 p2) = PFLe (Tp p1) (Tp p2)) by reflexivity;
  repeat first
    [ rewrite (T_and T Hi Hf)
    | rewrite (T_or T Hi Hf)
    | rewrite (T_not T Hi Hf)
    | rewrite (T_true T Hi Hf)
    | rewrite (T_eq T Tp Hl Hi Hf)
    | rewrite (T_ge T Tp Hl)
    | rewrite Hl
    | rewrite Hi ];
  clear Hi Hf Hl.

(** Push every transformer in the goal through the connectives, down to
    [Pterm]s, and compute the [Pterm]-level transformers. *)
Ltac ptransform :=
  unfold p_almost_sure, p_concentrated_unit, if_precondition, sum_precondition,
         while_body_post_upper, while_body_post_lower,
         fvar, tvar, tnat, pvar, pconst, cbool in *;
  cbn [finite_p_and] in *;
  repeat match goal with
  | |- context [@toss_pformula ?Dm ?b ?r _] =>
      progress commute_one (@toss_pformula Dm b r) (@toss_pterm Dm b r)
  | |- context [@subst_bool_pformula ?Dm ?b ?f _] =>
      progress commute_one (@subst_bool_pformula Dm b f) (@subst_bool_pterm Dm b f)
  | |- context [@subst_dom_pformula ?Dm ?x ?t _] =>
      progress commute_one (@subst_dom_pformula Dm x t) (@subst_dom_pterm Dm x t)
  | |- context [@subst_prob_pformula ?Dm ?y ?p _] =>
      progress commute_one (@subst_prob_pformula Dm y p) (@subst_prob_pterm Dm y p)
  | |- context [condition_pformula _ ?g] =>
      progress (rewrite ?(cond_and g), ?(cond_or g), ?(cond_not g), ?(cond_true g),
                        ?(cond_eq g), ?(cond_ge g), ?(cond_le g), ?(cond_impl g))
  end;
  cbn [toss_pterm subst_bool_pterm subst_dom_pterm subst_prob_pterm condition_pterm
       subst_bool_cformula subst_dom_cformula subst_dom_term
       c_and c_not c_or c_true c_iff c_le c_eq c_lt t_add t_sub t_mul t_mod] in *.

(** Decide equalities between concrete variable names. *)
Ltac vdec :=
  repeat match goal with
  | |- context [bool_program_var_eq_dec ?a ?a] =>
      let Hn := fresh in
      destruct (bool_program_var_eq_dec a a) as [_|Hn]; [|exfalso; apply Hn; reflexivity]
  | |- context [bool_program_var_eq_dec ?a ?b] =>
      let He := fresh in
      destruct (bool_program_var_eq_dec a b) as [He|_]; [discriminate He|]
  | |- context [dom_program_var_eq_dec ?a ?a] =>
      let Hn := fresh in
      destruct (dom_program_var_eq_dec a a) as [_|Hn]; [|exfalso; apply Hn; reflexivity]
  | |- context [dom_program_var_eq_dec ?a ?b] =>
      let He := fresh in
      destruct (dom_program_var_eq_dec a b) as [He|_]; [discriminate He|]
  | |- context [prob_logic_var_eq_dec ?a ?a] =>
      let Hn := fresh in
      destruct (prob_logic_var_eq_dec a a) as [_|Hn]; [|exfalso; apply Hn; reflexivity]
  | |- context [prob_logic_var_eq_dec ?a ?b] =>
      let He := fresh in
      destruct (prob_logic_var_eq_dec a b) as [He|_]; [discriminate He|]
  end.

(** Compute the syntactic transformers in a goal. *)
Ltac pcompute :=
  cbn [toss_pterm subst_bool_pterm subst_dom_pterm subst_prob_pterm condition_pterm
       subst_bool_cformula subst_dom_cformula subst_dom_term
       c_and c_not c_or c_true c_iff c_le c_eq c_lt t_add t_sub t_mul t_mod
       fvar tvar tnat cbool] in *.

Ltac ptrans :=
  ptransform; repeat progress (vdec; pcompute); cbn beta iota in *.

Ltac pvalid :=
  let ps := fresh "ps" in
  let Hps := fresh "Hps" in
  let H := fresh "H" in
  intros ps Hps;
  unfold p_ge, p_concentrated_unit, if_precondition, sum_precondition, pvar, pconst,
         while_body_post_upper, while_body_post_lower in *;
  cbn [finite_p_and] in *;
  rewrite ?psatisfies_true_iff in *;
  psimpl_goal;
  try (intros H; psimpl_in H);
  cbn [pterm_eval] in *.

(** Basic facts about every formula probability in the goal, for [lra]. *)
Ltac pr_facts ps Hps :=
  repeat match goal with
  | |- context [Pr[ps] ?g] =>
      lazymatch goal with
      | _ : 0 <= Pr[ps] g |- _ => fail
      | _ => pose proof (Pr_nonneg ps g); pose proof (Pr_le_true ps Hps g)
      end
  end;
  pose proof (Pr_true_le1 ps Hps).

(** * Derived rules *)

Section DerivedRules.
Implicit Types (pre post eta : PFormula) (c : Cmd).

Lemma HConseqLeft pre pre' c post :
  pformula_valid (PFImpl pre pre') -> hoare_derivable pre' c post ->
  hoare_derivable pre c post.
Proof. apply derive_pre. Qed.

Lemma HConseqRight pre c post post' :
  pformula_valid (PFImpl post post') -> hoare_derivable pre c post ->
  hoare_derivable pre c post'.
Proof. intros H1 H2; exact (derive_post pre c post post' H2 H1). Qed.

(** Exact IF. *)
Lemma HIfEq eta1 eta2 (beta gamma : CFormula) y1 y2 c1 c2 :
  hoare_derivable eta1 c1 (p_eq (PVar y1) (PProb gamma)) ->
  hoare_derivable eta2 c2 (p_eq (PVar y2) (PProb gamma)) ->
  hoare_derivable (if_precondition eta1 eta2 beta) (CIf beta c1 c2)
    (p_eq (PAdd (PVar y1) (PVar y2)) (PProb gamma)).
Proof. apply derive_if_eq. Qed.

(** Substituting a constant for a probabilistic logic variable removes it. *)
Lemma subst_prob_const_pterm_fresh y r (p : Pterm) :
  ~ prob_logic_var_occurs_pterm y (subst_prob_pterm y (PConst r) p).
Proof.
  induction p as [y'| | |p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try tauto.
  destruct (prob_logic_var_eq_dec y' y) as [->|Hne]; cbn; [tauto|].
  intros ->; apply Hne; reflexivity.
Qed.

Lemma subst_prob_const_fresh y r (eta : PFormula) :
  ~ prob_logic_var_occurs_pformula y (subst_prob_pformula y (PConst r) eta).
Proof.
  induction eta as [p1 p2| |e1 IH1 e2 IH2]; cbn; try tauto.
  pose proof (subst_prob_const_pterm_fresh y r p1);
  pose proof (subst_prob_const_pterm_fresh y r p2); tauto.
Qed.

(** Instantiate a probabilistic logic variable [y] by a constant [r] on both
    sides of a derivable triple (ELIMV, FREE and AND). *)
Lemma HInstantiate y r pre c post :
  hoare_derivable pre c post ->
  hoare_derivable (subst_prob_pformula y (PConst r) pre) c
                  (subst_prob_pformula y (PConst r) post).
Proof.
  intros H. apply HElimv.
  - eapply derive_post.
    + apply derive_analytical_frame with (frame := p_eq (PVar y) (PConst r)).
      * cbn; tauto.
      * exact H.
    + intros ps Hps Hp. apply psatisfies_and in Hp as [Hp Hy].
      apply psatisfies_eq in Hy. cbn in Hy.
      apply (subst_prob_pformula_correct y (PConst r) post ps). cbn.
      unfold pstate_update_prob. rewrite <- Hy, update_prob_same.
      destruct ps; exact Hp.
  - cbn; tauto.
  - apply subst_prob_const_fresh.
Qed.

End DerivedRules.

(** * While-rule side conditions *)

(** Reduce [forall i, i < m -> P i] to the cases [P 0], ..., [P (m-1)]. *)
Ltac below_cases :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi;
  repeat (destruct i as [|i]; [|apply (proj2 (PeanoNat.Nat.succ_lt_mono _ _)) in Hi]);
  try (exfalso; lia).

Ltac while_side :=
  unfold while_regions_cover, while_regions_in_guard, while_regions_disjoint,
         while_progress, while_upper_solution, while_lower_solution, cformula_valid;
  cbn [finite_c_or finite_r_sum].

