(** Soundness of the atomic rules: [ASGR], [ASGB], [TOSS], and the
    invalid-rate toss rule. *)
From Stdlib Require Import Reals.
Require Import PHL.
Require Import Soundness.AssertionFacts Soundness.TransformerAssertions.

Section AtomicRules.
Context {D : Domain}.
Local Notation PFormula := (PFormula D).

Lemma hoare_valid_dom_assign (eta : PFormula) x t :
  hoare_valid (subst_dom_pformula x t eta) (CDomAssign x t) eta.
Proof. intros ps _ H. apply subst_dom_pformula_run. exact H. Qed.

Lemma hoare_valid_bool_assign (eta : PFormula) b beta :
  hoare_valid (subst_bool_pformula b beta eta) (CBoolAssign b beta) eta.
Proof. intros ps _ H. apply subst_bool_pformula_run. exact H. Qed.

Lemma hoare_valid_bool_toss (eta : PFormula) b r :
  coin_probability_valid r ->
  hoare_valid (toss_pformula b r eta) (CBoolToss b r) eta.
Proof. intros hr ps hps H. apply (toss_pformula_run b eta hr hps). exact H. Qed.

Lemma hoare_valid_bool_toss_invalid b r :
  ~ coin_probability_valid r ->
  hoare_valid (D := D) p_true (CBoolToss b r) (p_eq (PProb c_true) (PConst 0)).
Proof.
  intros hr ps _ _. apply psatisfies_eq. cbn.
  apply run_toss_invalid_mass. exact hr.
Qed.

End AtomicRules.
