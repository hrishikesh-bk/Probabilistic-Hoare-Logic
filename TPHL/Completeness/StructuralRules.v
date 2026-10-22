(** Derived rules used by completeness; no new Hoare constructors.  Adapted
    from CPHL's Completeness/StructuralRules.v, with the exact IF rule derived
    from [IF<=], [IF>=] and [AND]. *)
From Stdlib Require Import List Reals Lra.
Require Import PHL Soundness.AssertionFacts Completeness.Freshness.
Import ListNotations.

Section DerivedRules.
Context {D : Domain}.
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).
Local Notation Pstate := (Pstate D).
Implicit Types (pre post eta : PFormula) (C : Cmd D).

Lemma derive_pre pre pre' C post :
  pformula_valid (PFImpl pre pre') -> hoare_derivable pre' C post ->
  hoare_derivable pre C post.
Proof.
  intros Himp Hder; eapply HConseq; [exact Himp | exact Hder |].
  intros ps Hps H; exact H.
Qed.

Lemma derive_post pre C post post' :
  hoare_derivable pre C post -> pformula_valid (PFImpl post post') ->
  hoare_derivable pre C post'.
Proof.
  intros Hder Himp; eapply HConseq; [| exact Hder | exact Himp].
  intros ps Hps H; exact H.
Qed.

Lemma derive_true pre C : hoare_derivable pre C p_true.
Proof.
  eapply derive_pre with (pre' := p_true).
  - intros ps Hps H; apply psatisfies_true.
  - apply HFree; cbn; auto.
Qed.

(** Analytical assertions are framed for free. *)
Lemma derive_analytical_frame pre C post frame :
  pformula_analytical frame -> hoare_derivable pre C post ->
  hoare_derivable (p_and pre frame) C (p_and post frame).
Proof.
  intros Hframe Hder; apply HAnd.
  - eapply derive_pre; [| exact Hder].
    intros ps Hps H; apply psatisfies_and in H; tauto.
  - eapply derive_pre with (pre' := frame).
    + intros ps Hps H; apply psatisfies_and in H; tauto.
    + apply HFree; exact Hframe.
Qed.

Fixpoint pformula_conjunction (posts : list PFormula) : PFormula :=
  match posts with
  | [] => p_true
  | post :: rest => p_and post (pformula_conjunction rest)
  end.

Lemma psatisfies_conjunction ps posts :
  psatisfies ps (pformula_conjunction posts) <->
  forall post, In post posts -> psatisfies ps post.
Proof.
  induction posts as [|post rest IH]; cbn [pformula_conjunction].
  - split; [intros _ eta H; inversion H | intros _; apply psatisfies_true].
  - rewrite psatisfies_and, IH; cbn; split.
    + intros [Hpost Hrest] eta [<- | H]; auto.
    + intro H; split; [apply H; auto | intros eta Hin; apply H; auto].
Qed.

Lemma derive_conjunction pre C posts :
  (forall post, In post posts -> hoare_derivable pre C post) ->
  hoare_derivable pre C (pformula_conjunction posts).
Proof.
  induction posts as [|post rest IH]; intro H; cbn [pformula_conjunction].
  - apply derive_true.
  - apply HAnd; [apply H; cbn; auto | apply IH; intros eta Hin; apply H; cbn; auto].
Qed.

(** Bindings [y = p] eliminated by repeated [ELIMV]. *)
Definition ProbBindings := list (ProbLogicVar * Pterm).

Fixpoint bindings_precondition (bindings : ProbBindings) (pre : PFormula) : PFormula :=
  match bindings with
  | [] => pre
  | (y,p) :: rest => p_and (bindings_precondition rest pre) (p_eq (PVar y) p)
  end.

Fixpoint substitute_bindings (bindings : ProbBindings) (pre : PFormula) : PFormula :=
  match bindings with
  | [] => pre
  | (y,p) :: rest => substitute_bindings rest (subst_prob_pformula y p pre)
  end.

Definition independent_bindings (bindings : ProbBindings) : Prop :=
  NoDup (map (@fst ProbLogicVar Pterm) bindings) /\
  forall y p z r, In (y,p) bindings -> In (z,r) bindings ->
    ~ prob_logic_var_occurs_pterm y r.

Lemma substitute_bindings_precondition y p bindings pre :
  (forall z r, In (z,r) bindings ->
    z <> y /\ ~ prob_logic_var_occurs_pterm y r) ->
  subst_prob_pformula y p (bindings_precondition bindings pre) =
  bindings_precondition bindings (subst_prob_pformula y p pre).
Proof.
  induction bindings as [|[z r] rest IH]; intro H; [reflexivity |].
  change (p_and (subst_prob_pformula y p (bindings_precondition rest pre))
    (subst_prob_pformula y p (p_eq (PVar z) r)) =
    p_and (bindings_precondition rest (subst_prob_pformula y p pre)) (p_eq (PVar z) r)).
  rewrite IH by (intros; apply H; cbn; auto).
  rewrite (subst_prob_pformula_fresh y p (p_eq (PVar z) r)); [reflexivity |].
  destruct (H z r (or_introl eq_refl)) as [Hneq Hfresh].
  cbn [p_eq p_and p_not prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm];
    intuition congruence.
Qed.

Lemma derive_eliminate_bindings bindings pre C post :
  independent_bindings bindings ->
  (forall y p, In (y,p) bindings -> ~ prob_logic_var_occurs_pformula y post) ->
  hoare_derivable (bindings_precondition bindings pre) C post ->
  hoare_derivable (substitute_bindings bindings pre) C post.
Proof.
  revert pre; induction bindings as [|[y p] rest IH]; intros pre Hind Hpost Hder.
  - exact Hder.
  - destruct Hind as [Hdistinct Hfresh].
    inversion Hdistinct as [|? ? Hnotin Hnodup]; subst.
    assert (Htail : independent_bindings rest).
    { split; [exact Hnodup |].
      intros z r w t Hz Hw; apply (Hfresh z r w t); cbn; auto. }
    assert (Hy : ~ prob_logic_var_occurs_pterm y p).
    { apply (Hfresh y p y p); cbn; auto. }
    assert (HyPost : ~ prob_logic_var_occurs_pformula y post).
    { apply (Hpost y p); cbn; auto. }
    pose proof (HElimv (bindings_precondition rest pre) post y p C Hder Hy HyPost) as Helim.
    rewrite substitute_bindings_precondition in Helim.
    + cbn [substitute_bindings]; apply IH; [exact Htail | | exact Helim].
      intros z r Hz; apply (Hpost z r); cbn; auto.
    + intros z r Hz; split.
      * intro Heq; subst z; apply Hnotin.
        apply in_map_iff; exists (y,r); split; [reflexivity | exact Hz].
      * apply (Hfresh y p z r); cbn; auto.
Qed.

Lemma eq_to_le ps (p1 p2 : Pterm) :
  psatisfies ps (p_eq p1 p2) -> psatisfies ps (PFLe p1 p2) /\ psatisfies ps (PFLe p2 p1).
Proof. intros H; apply psatisfies_eq in H; cbn; lra. Qed.

(** Exact SUM, from [SUM<=] and [SUM>=]. *)
Lemma derive_sum_eq eta1 eta2 (gamma1 gamma2 gamma : CFormula D) y1 y2 C :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_derivable (p_and eta1 (p_almost_sure gamma1)) C (p_eq (PVar y1) (PProb gamma)) ->
  hoare_derivable (p_and eta2 (p_almost_sure gamma2)) C (p_eq (PVar y2) (PProb gamma)) ->
  hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) C
    (p_eq (PAdd (PVar y1) (PVar y2)) (PProb gamma)).
Proof.
  intros Hdis H1 H2. apply HAnd.
  - apply HSumLe; [exact Hdis | |].
    + eapply derive_post; [exact H1 |]. intros ps _ H; apply eq_to_le in H; tauto.
    + eapply derive_post; [exact H2 |]. intros ps _ H; apply eq_to_le in H; tauto.
  - apply HSumGe; [exact Hdis | |].
    + eapply derive_post; [exact H1 |]. intros ps _ H; apply eq_to_le in H; tauto.
    + eapply derive_post; [exact H2 |]. intros ps _ H; apply eq_to_le in H; tauto.
Qed.

(** Exact IF, from [IF<=] and [IF>=]. *)
Lemma derive_if_eq eta1 eta2 (beta gamma : CFormula D) y1 y2 C1 C2 :
  hoare_derivable eta1 C1 (p_eq (PVar y1) (PProb gamma)) ->
  hoare_derivable eta2 C2 (p_eq (PVar y2) (PProb gamma)) ->
  hoare_derivable (if_precondition eta1 eta2 beta) (CIf beta C1 C2)
    (p_eq (PAdd (PVar y1) (PVar y2)) (PProb gamma)).
Proof.
  intros H1 H2. apply HAnd.
  - apply HIfLe.
    + eapply derive_post; [exact H1 |]. intros ps _ H; apply eq_to_le in H; tauto.
    + eapply derive_post; [exact H2 |]. intros ps _ H; apply eq_to_le in H; tauto.
  - apply HIfGe.
    + eapply derive_post; [exact H1 |]. intros ps _ H; apply eq_to_le in H; tauto.
    + eapply derive_post; [exact H2 |]. intros ps _ H; apply eq_to_le in H; tauto.
Qed.

End DerivedRules.
