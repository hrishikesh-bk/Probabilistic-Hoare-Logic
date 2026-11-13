(** Metatheory of PPL satisfaction: derived connectives, extensionality in
    the measure, analytical formulas, and probabilistic logic variables. *)
From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
From mathcomp Require boolp.
Require Import PHL.

Section AssertionFacts.
Context {D : Domain}.

Local Notation Pstate := (Pstate D).
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).
Implicit Types (ps : Pstate) (eta : PFormula) (p q : Pterm) (gamma : CFormula D).

(** ** Derived connectives *)

Lemma psatisfies_true ps : psatisfies ps p_true.
Proof. cbn. tauto. Qed.

Lemma psatisfies_not ps eta : psatisfies ps (p_not eta) <-> ~ psatisfies ps eta.
Proof. cbn. tauto. Qed.

Lemma psatisfies_and ps eta1 eta2 :
  psatisfies ps (p_and eta1 eta2) <-> psatisfies ps eta1 /\ psatisfies ps eta2.
Proof. cbn. split; [intro H | tauto]. split; apply Classical_Prop.NNPP; tauto. Qed.

Lemma psatisfies_or ps eta1 eta2 :
  psatisfies ps (p_or eta1 eta2) <-> psatisfies ps eta1 \/ psatisfies ps eta2.
Proof. cbn. split; [intro H | tauto]. destruct (Classical_Prop.classic (psatisfies ps eta1)); tauto. Qed.

Lemma psatisfies_impl ps eta1 eta2 :
  psatisfies ps (PFImpl eta1 eta2) <-> (psatisfies ps eta1 -> psatisfies ps eta2).
Proof. reflexivity. Qed.

Lemma psatisfies_le ps p1 p2 :
  psatisfies ps (PFLe p1 p2) <-> pterm_eval p1 ps <= pterm_eval p2 ps.
Proof. reflexivity. Qed.

Lemma psatisfies_eq ps p1 p2 :
  psatisfies ps (p_eq p1 p2) <-> pterm_eval p1 ps = pterm_eval p2 ps.
Proof. unfold p_eq. rewrite psatisfies_and. cbn. split; [intros []; lra | intros ->; lra]. Qed.

Lemma psatisfies_almost_sure ps gamma :
  psatisfies ps (p_almost_sure gamma) <->
  measure_of (pstate_measure ps) (formula_assertion gamma) =
  measure_of (pstate_measure ps) (formula_assertion c_true).
Proof. apply psatisfies_eq. Qed.

Lemma formula_assertion_true : formula_assertion (D := D) c_true = (fun _ => True).
Proof.
  apply functional_extensionality; intro v.
  apply boolp.propext. cbn. tauto.
Qed.

Lemma finite_p_and_spec ps m (formulas : nat -> PFormula) :
  psatisfies ps (finite_p_and m formulas) <->
  forall j, (j < m)%nat -> psatisfies ps (formulas j).
Proof.
  induction m as [|m IH]; cbn [finite_p_and].
  - split; [intros _ j Hj; lia | intros _; apply psatisfies_true].
  - rewrite psatisfies_and, IH. split.
    + intros [H1 H2] j Hj. destruct (Nat.eq_dec j m) as [->|Hne]; [exact H2|].
      apply H1. lia.
    + intros H. split; [intros j Hj; apply H; lia | apply H; lia].
Qed.

(** ** Extensionality: satisfaction depends only on formula masses and rho *)

Definition same_masses (ps1 ps2 : Pstate) : Prop :=
  (forall gamma : CFormula D,
     measure_of (pstate_measure ps1) (formula_assertion gamma) =
     measure_of (pstate_measure ps2) (formula_assertion gamma)) /\
  pstate_prob_logic_values ps1 = pstate_prob_logic_values ps2.

Lemma pterm_eval_same_masses ps1 ps2 p :
  same_masses ps1 ps2 -> pterm_eval p ps1 = pterm_eval p ps2.
Proof.
  intros [Hm Hr]. induction p; cbn; congruence.
Qed.

Lemma psatisfies_same_masses ps1 ps2 eta :
  same_masses ps1 ps2 -> psatisfies ps1 eta <-> psatisfies ps2 eta.
Proof.
  intros H. induction eta; cbn.
  - rewrite !(pterm_eval_same_masses _ _ _ H). reflexivity.
  - reflexivity.
  - tauto.
Qed.

(** ** Analytical formulas do not depend on the measure *)

Lemma pterm_eval_analytical p ps1 ps2 :
  pterm_analytical p ->
  pstate_prob_logic_values ps1 = pstate_prob_logic_values ps2 ->
  pterm_eval p ps1 = pterm_eval p ps2.
Proof.
  intros Ha Hr. induction p; cbn in *; try contradiction.
  - rewrite Hr; reflexivity.
  - reflexivity.
  - destruct Ha; f_equal; auto.
  - destruct Ha; f_equal; auto.
Qed.

Lemma psatisfies_analytical eta ps1 ps2 :
  pformula_analytical eta ->
  pstate_prob_logic_values ps1 = pstate_prob_logic_values ps2 ->
  psatisfies ps1 eta <-> psatisfies ps2 eta.
Proof.
  intros Ha Hr. induction eta; cbn in *.
  - destruct Ha. rewrite !(pterm_eval_analytical _ ps1 ps2); tauto.
  - reflexivity.
  - destruct Ha. rewrite IHeta1, IHeta2 by assumption. reflexivity.
Qed.

(** ** Probabilistic logic variables *)

Definition update_prob (rho : ProbLogicVar -> R) (y : ProbLogicVar) (r : R) :
  ProbLogicVar -> R :=
  fun y' => if prob_logic_var_eq_dec y' y then r else rho y'.

Definition pstate_update_prob (ps : Pstate) (y : ProbLogicVar) (r : R) : Pstate :=
  {| pstate_measure := pstate_measure ps;
     pstate_prob_logic_values := update_prob (pstate_prob_logic_values ps) y r |}.

Lemma subst_prob_pterm_correct y q p ps :
  pterm_eval (subst_prob_pterm y q p) ps =
  pterm_eval p (pstate_update_prob ps y (pterm_eval q ps)).
Proof.
  induction p; cbn; try congruence.
  unfold update_prob. destruct (prob_logic_var_eq_dec y0 y); reflexivity.
Qed.

Lemma subst_prob_pformula_correct y q eta ps :
  psatisfies ps (subst_prob_pformula y q eta) <->
  psatisfies (pstate_update_prob ps y (pterm_eval q ps)) eta.
Proof.
  induction eta; cbn.
  - rewrite !subst_prob_pterm_correct. reflexivity.
  - reflexivity.
  - rewrite IHeta1, IHeta2. reflexivity.
Qed.

(** A term or formula that does not mention [y] ignores the value of [y]. *)
Lemma pterm_eval_update_fresh y r p ps :
  ~ prob_logic_var_occurs_pterm y p ->
  pterm_eval p (pstate_update_prob ps y r) = pterm_eval p ps.
Proof.
  intros Hy. induction p; cbn in *; try reflexivity.
  - unfold update_prob. destruct (prob_logic_var_eq_dec y0 y); [|reflexivity].
    subst; contradiction Hy; reflexivity.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma psatisfies_update_fresh y r eta ps :
  ~ prob_logic_var_occurs_pformula y eta ->
  psatisfies (pstate_update_prob ps y r) eta <-> psatisfies ps eta.
Proof.
  intros Hy. induction eta; cbn in *.
  - rewrite !pterm_eval_update_fresh by tauto. reflexivity.
  - reflexivity.
  - rewrite IHeta1, IHeta2 by tauto. reflexivity.
Qed.

Lemma update_prob_same rho y : update_prob rho y (rho y) = rho.
Proof.
  apply functional_extensionality; intro y'. unfold update_prob.
  destruct (prob_logic_var_eq_dec y' y); [subst|]; reflexivity.
Qed.

End AssertionFacts.
