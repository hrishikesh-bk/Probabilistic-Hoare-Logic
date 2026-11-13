(** Soundness of the structural rules: [Pr-FREE], [SKIP], [SEQ], [CONS],
    [OR], [AND], [ELIMV].  Each lemma takes the semantic validity of the
    premises and returns the validity of the conclusion. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration PHL.
Require Import Soundness.CommandFacts Soundness.AssertionFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].

Section StructuralRules.
Context {D : Domain}.
Local Notation Pstate := (Pstate D).
Local Notation PFormula := (PFormula D).
Local Notation Pterm := (Pterm D).
Implicit Types (ps : Pstate) (eta : PFormula) (p : Pterm) (s : Cmd D).

(** [skip] and sequencing preserve all formula masses. *)
Lemma run_skip_same ps : same_masses (run CSkip ps) ps.
Proof.
  split; [|reflexivity]. intros gamma.
  unfold measure_of, ConcreteMeasure.event_mass. f_equal.
  exact (transform_skip (pstate_measure ps) (formula_assertion gamma)).
Qed.

Lemma run_seq_same s1 s2 ps : pstate_admissible ps ->
  same_masses (run (CSeq s1 s2) ps) (run s2 (run s1 ps)).
Proof.
  intros hps. split; [|reflexivity]. intros gamma.
  unfold measure_of, ConcreteMeasure.event_mass. f_equal.
  exact (transform_sequence (CommandSemantics.denote s1) (CommandSemantics.denote s2)
           (formula_assertion gamma) hps).
Qed.

Lemma hoare_valid_free eta s :
  pformula_analytical eta -> hoare_valid eta s eta.
Proof.
  intros Ha ps _ H. apply (psatisfies_analytical eta (run s ps) ps Ha); [reflexivity | exact H].
Qed.

Lemma hoare_valid_skip eta : hoare_valid eta CSkip eta.
Proof.
  intros ps _ H. apply (psatisfies_same_masses (run CSkip ps) ps eta (run_skip_same ps)).
  exact H.
Qed.

Lemma hoare_valid_seq eta1 eta2 eta3 s1 s2 :
  hoare_valid eta1 s1 eta2 -> hoare_valid eta2 s2 eta3 ->
  hoare_valid eta1 (CSeq s1 s2) eta3.
Proof.
  intros H1 H2 ps hps H.
  apply (psatisfies_same_masses _ _ eta3 (run_seq_same s1 s2 hps)).
  apply H2; [apply run_admissible; exact hps | apply H1; assumption].
Qed.

Lemma hoare_valid_conseq eta0 eta1 eta2 eta3 s :
  pformula_valid (PFImpl eta0 eta1) -> hoare_valid eta1 s eta2 ->
  pformula_valid (PFImpl eta2 eta3) -> hoare_valid eta0 s eta3.
Proof.
  intros H01 H H23 ps hps H0.
  apply (H23 (run s ps) (run_admissible s hps)).
  apply H; [exact hps | exact (H01 ps hps H0)].
Qed.

Lemma hoare_valid_or eta0 eta1 eta2 s :
  hoare_valid eta0 s eta2 -> hoare_valid eta1 s eta2 ->
  hoare_valid (p_or eta0 eta1) s eta2.
Proof.
  intros H0 H1 ps hps H. apply psatisfies_or in H.
  destruct H as [H|H]; [exact (H0 ps hps H) | exact (H1 ps hps H)].
Qed.

Lemma hoare_valid_and eta0 eta1 eta2 s :
  hoare_valid eta0 s eta1 -> hoare_valid eta0 s eta2 ->
  hoare_valid eta0 s (p_and eta1 eta2).
Proof.
  intros H1 H2 ps hps H. apply psatisfies_and. split; [exact (H1 ps hps H) | exact (H2 ps hps H)].
Qed.

(** [ELIMV]: instantiate the eliminated variable with the value of [p]. *)
Lemma hoare_valid_elimv eta1 eta2 y p s :
  hoare_valid (p_and eta1 (p_eq (PVar y) p)) s eta2 ->
  ~ prob_logic_var_occurs_pterm y p ->
  ~ prob_logic_var_occurs_pformula y eta2 ->
  hoare_valid (subst_prob_pformula y p eta1) s eta2.
Proof.
  intros H Hp Heta ps hps Hpre.
  apply subst_prob_pformula_correct in Hpre.
  set (ps' := pstate_update_prob ps y (pterm_eval p ps)).
  assert (Hy : psatisfies ps' (p_eq (PVar y) p)).
  { apply psatisfies_eq. unfold ps'. rewrite (pterm_eval_update_fresh y _ p ps Hp).
    cbn. unfold update_prob. destruct (prob_logic_var_eq_dec y y) as [_|n]; [reflexivity|].
    contradiction n; reflexivity. }
  assert (Hout : psatisfies (run s ps') eta2).
  { apply H; [exact hps | apply psatisfies_and; split; assumption]. }
  change (psatisfies (pstate_update_prob (run s ps) y (pterm_eval p ps)) eta2) in Hout.
  exact (proj1 (psatisfies_update_fresh y _ eta2 (run s ps) Heta) Hout).
Qed.

End StructuralRules.
