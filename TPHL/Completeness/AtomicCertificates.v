(** Certificates for skip, assignments, and tosses (both valid and invalid
    rates).  Adapted from CPHL's Completeness/AtomicCertificates.v. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require boolp.
Require Import MeasureIntegration PHL.
Require Import Soundness.AssertionFacts Soundness.TransformerAssertions
  Soundness.StructuralRules Soundness.SplitRules.
Require Import Completeness.Interface Completeness.StructuralRules.

Section AtomicCertificates.
Context {D : Domain}.
Local Notation Pterm := (Pterm D).

Definition skip_transformer (gamma : CFormula D) : Pterm := PProb gamma.
Definition dom_assign_transformer x t (gamma : CFormula D) : Pterm :=
  subst_dom_pterm x t (PProb gamma).
Definition bool_assign_transformer b beta (gamma : CFormula D) : Pterm :=
  subst_bool_pterm b beta (PProb gamma).
Definition valid_toss_transformer b r (gamma : CFormula D) : Pterm :=
  toss_pterm b r (PProb gamma).
Definition invalid_toss_transformer (_ : CFormula D) : Pterm := PConst 0.

Theorem skip_certificate : certificate CSkip skip_transformer.
Proof.
  constructor.
  - intros gamma y; cbn; tauto.
  - intros ps gamma _. symmetry.
    exact (pterm_eval_same_masses _ _ (PProb gamma) (run_skip_same ps)).
  - intros gamma y; apply HSkip.
Qed.

Theorem dom_assign_certificate x t :
  certificate (CDomAssign x t) (dom_assign_transformer x t).
Proof.
  constructor.
  - intros gamma y; cbn; tauto.
  - intros ps gamma _; apply subst_dom_pterm_run.
  - intros gamma y.
    change (hoare_derivable (subst_dom_pformula x t (p_eq (PVar y) (PProb gamma)))
      (CDomAssign x t) (p_eq (PVar y) (PProb gamma))).
    apply HDomAssign.
Qed.

Theorem bool_assign_certificate b beta :
  certificate (CBoolAssign b beta) (bool_assign_transformer b beta).
Proof.
  constructor.
  - intros gamma y; cbn; tauto.
  - intros ps gamma _; apply subst_bool_pterm_run.
  - intros gamma y.
    change (hoare_derivable (subst_bool_pformula b beta (p_eq (PVar y) (PProb gamma)))
      (CBoolAssign b beta) (p_eq (PVar y) (PProb gamma))).
    apply HBoolAssign.
Qed.

Theorem valid_toss_certificate b r : coin_probability_valid r ->
  certificate (CBoolToss b r) (valid_toss_transformer b r).
Proof.
  intro Hr; constructor.
  - intros gamma y; cbn; tauto.
  - intros ps gamma Hps; apply toss_pterm_run; assumption.
  - intros gamma y.
    change (hoare_derivable (toss_pformula b r (p_eq (PVar y) (PProb gamma)))
      (CBoolToss b r) (p_eq (PVar y) (PProb gamma))).
    apply HBoolToss; exact Hr.
Qed.

(** Zero total mass forces every formula mass to vanish. *)
Lemma zero_mass_formula (gamma : CFormula D) ps : pstate_admissible ps ->
  psatisfies ps (p_eq (PProb c_true) (PConst 0)) ->
  pterm_eval (PProb gamma) ps = 0%R.
Proof.
  intros Hps Hmass; apply psatisfies_eq in Hmass; cbn in *.
  pose proof (measure_nonnegative (pstate_measure ps) (formula_assertion gamma)).
  assert (measure_of (pstate_measure ps) (formula_assertion gamma) <=
          measure_of (pstate_measure ps) (formula_assertion c_true))%R.
  { apply measure_of_monotone; [exact Hps |]. intros v _. cbn. tauto. }
  lra.
Qed.

Theorem invalid_toss_certificate b r : ~ coin_probability_valid r ->
  certificate (CBoolToss b r) invalid_toss_transformer.
Proof.
  intro Hr; constructor.
  - intros gamma y; cbn; tauto.
  - intros ps gamma Hps; cbn [invalid_toss_transformer pterm_eval].
    symmetry. apply run_toss_invalid_mass. exact Hr.
  - intros gamma y.
    eapply derive_pre with (pre' := p_and p_true (p_eq (PVar y) (PConst 0))).
    + intros ps Hps H; apply psatisfies_and; split; [apply psatisfies_true | exact H].
    + eapply derive_post.
      * apply derive_analytical_frame; [cbn; tauto |].
        apply HBoolTossInvalid; exact Hr.
      * intros ps Hps H; apply psatisfies_and in H.
        destruct H as [Hmass Hy]; apply psatisfies_eq in Hy.
        apply psatisfies_eq; rewrite (zero_mass_formula gamma ps Hps Hmass); exact Hy.
Qed.

Definition toss_transformer b r : CFormula D -> Pterm :=
  if boolp.pselect (coin_probability_valid r)
  then valid_toss_transformer b r
  else invalid_toss_transformer.

Theorem toss_certificate b r : certificate (CBoolToss b r) (toss_transformer b r).
Proof.
  unfold toss_transformer; destruct (boolp.pselect _) as [Hr | Hr].
  - apply valid_toss_certificate; exact Hr.
  - apply invalid_toss_certificate; exact Hr.
Qed.

End AtomicCertificates.
