(** Soundness of the rules that split the input measure: [IF<=], [IF>=]
    (by the guard) and [SUM<=], [SUM>=] (by two disjoint formulas). *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration PHL.
Require Import Soundness.StateFacts Soundness.CommandFacts Soundness.AssertionFacts
  Soundness.TransformerAssertions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].

Section Masses.
Context {D : Domain}.
Local Notation Pstate := (Pstate D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Open Scope R_scope.

Lemma restrict_measure_of ps gamma (A : Assertion D) :
  measure_of (pstate_measure (pstate_restrict ps gamma)) A =
  measure_of (pstate_measure ps) (fun v => A v /\ satisfies v gamma).
Proof. reflexivity. Qed.

(** IF: the output is the sum of the two branch outputs on the restricted
    inputs. *)
Lemma run_if_mass beta s1 s2 ps (A : Assertion D) : pstate_admissible ps ->
  measure_of (pstate_measure (run (CIf beta s1 s2) ps)) A =
  measure_of (pstate_measure (run s1 (pstate_restrict ps beta))) A +
  measure_of (pstate_measure (run s2 (pstate_restrict ps (c_not beta)))) A.
Proof.
  intros hps. apply EFin_inj.
  have h0 := run_admissible (CIf beta s1 s2) hps.
  have h1 := run_admissible s1 (restrict_admissible beta hps).
  have h2 := run_admissible s2 (restrict_admissible (c_not beta) hps).
  rewrite EFinD !measure_ofE //.
  exact (transform_branch beta (CommandSemantics.denote s1)
           (CommandSemantics.denote s2) (pstate_measure ps) A).
Qed.

Lemma measure_of_monotone (mu : carrier) (A B : Assertion D) :
  ConcreteMeasure.Subprob mu -> (forall v, A v -> B v) ->
  measure_of mu A <= measure_of mu B.
Proof.
  intros h hAB. apply/Rstruct.RleP.
  apply ConcreteMeasure.event_monotone; try exact: all_measurable.
  - exact: ConcreteMeasure.subprob_finite.
  - exact hAB.
Qed.

Lemma measure_of_null_subset (mu : carrier) (A B : Assertion D) :
  ConcreteMeasure.Subprob mu -> measure_of mu B = 0 -> (forall v, A v -> B v) ->
  measure_of mu A = 0.
Proof.
  intros h hB hAB. pose proof (measure_of_monotone h hAB).
  pose proof (measure_nonnegative mu A). lra.
Qed.

(** If [Box S] holds then the complement of [S] is null. *)
Lemma measure_of_complement_null (mu : carrier) (S : CFormula D) :
  ConcreteMeasure.Subprob mu ->
  measure_of mu (formula_assertion S) = measure_of mu (formula_assertion c_true) ->
  measure_of mu (fun v => ~ satisfies v S) = 0.
Proof.
  intros h hS.
  assert (Hsum := measure_additive mu (formula_assertion S) (fun v => ~ satisfies v S)
                    (ConcreteMeasure.subprob_finite h) (fun v H => proj2 H (proj1 H))).
  rewrite (measure_extensional mu (fun v => formula_assertion S v \/ ~ satisfies v S)
             (formula_assertion c_true)) in Hsum.
  - intros v. split; [intros _; apply satisfies_true | intros _; apply satisfies_dec].
  - lra.
Qed.

(** SUM: with [S = gamma1 \/ gamma2] almost sure and the two pieces disjoint,
    the input is the sum of its two restrictions. *)
Lemma split_mass (mu : carrier) (gamma1 gamma2 : CFormula D) (B : Assertion D) :
  ConcreteMeasure.Subprob mu ->
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  measure_of mu (formula_assertion (c_or gamma1 gamma2)) =
    measure_of mu (formula_assertion c_true) ->
  measure_of mu B =
  measure_of mu (fun v => B v /\ satisfies v gamma1) +
  measure_of mu (fun v => B v /\ satisfies v gamma2).
Proof.
  intros h hdisj hS.
  have hfin := ConcreteMeasure.subprob_finite h.
  have hnull := measure_of_complement_null h hS.
  have hdis v : ~ (satisfies v gamma1 /\ satisfies v gamma2).
  { intros H. apply (hdisj v). apply satisfies_and. exact H. }
  have hext : forall v, B v <->
      (((B v /\ satisfies v gamma1) \/ (B v /\ satisfies v gamma2)) \/
       (B v /\ ~ satisfies v (c_or gamma1 gamma2))).
  { intros v. rewrite satisfies_or.
    destruct (satisfies_dec v gamma1), (satisfies_dec v gamma2); tauto. }
  have hd1 : forall v, ~ ((B v /\ satisfies v gamma1) /\ (B v /\ satisfies v gamma2)).
  { intros v [[_ H1] [_ H2]]. exact (hdis v (conj H1 H2)). }
  have hd2 : forall v, ~ (((B v /\ satisfies v gamma1) \/ (B v /\ satisfies v gamma2)) /\
                         (B v /\ ~ satisfies v (c_or gamma1 gamma2))).
  { intros v [[[_ H]|[_ H]] [_ Hn]]; apply Hn; apply satisfies_or; [left|right]; exact H. }
  have hz : measure_of mu (fun v => B v /\ ~ satisfies v (c_or gamma1 gamma2)) = 0.
  { apply (measure_of_null_subset h hnull). intros v [_ H]; exact H. }
  rewrite (measure_extensional mu _ _ hext) (measure_additive mu _ _ hfin hd2)
    (measure_additive mu _ _ hfin hd1) hz.
  lra.
Qed.

Lemma run_split_mass s ps (gamma1 gamma2 : CFormula D) (A : Assertion D) :
  pstate_admissible ps ->
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  psatisfies ps (p_almost_sure (c_or gamma1 gamma2)) ->
  measure_of (pstate_measure (run s ps)) A =
  measure_of (pstate_measure (run s (pstate_restrict ps gamma1))) A +
  measure_of (pstate_measure (run s (pstate_restrict ps gamma2))) A.
Proof.
  intros hps hdisj hS. apply psatisfies_almost_sure in hS.
  have h1 := run_admissible s (restrict_admissible gamma1 hps).
  have h2 := run_admissible s (restrict_admissible gamma2 hps).
  have h0 := run_admissible s hps.
  apply EFin_inj. rewrite EFinD !measure_ofE //.
  set mu := pstate_measure ps.
  set r1 := pstate_measure (pstate_restrict ps gamma1).
  set r2 := pstate_measure (pstate_restrict ps gamma2).
  have hsplit : forall B, mu B = measure_add r1 r2 B.
  { move=> B. rewrite measure_addE.
    have hr1 := restrict_admissible gamma1 hps.
    have hr2 := restrict_admissible gamma2 hps.
    rewrite -(measure_ofE B hps) -(measure_ofE B hr1) -(measure_ofE B hr2) -EFinD.
    congr (_%:E).
    exact (split_mass B hps hdisj hS). }
  rewrite /transform_cmd (transform_ext _ hsplit) transform_add.
  reflexivity.
Qed.

End Masses.

Section SplitRules.
Context {D : Domain}.
Local Notation PFormula := (PFormula D).
Local Open Scope R_scope.

Lemma hoare_valid_if_le (eta1 eta2 : PFormula) beta gamma y1 y2 s1 s2 :
  hoare_valid eta1 s1 (PFLe (PVar y1) (PProb gamma)) ->
  hoare_valid eta2 s2 (PFLe (PVar y2) (PProb gamma)) ->
  hoare_valid (if_precondition eta1 eta2 beta) (CIf beta s1 s2)
    (PFLe (PAdd (PVar y1) (PVar y2)) (PProb gamma)).
Proof.
  intros H1 H2 ps hps Hpre.
  apply psatisfies_and in Hpre; destruct Hpre as [Hp1 Hp2].
  apply condition_pformula_correct in Hp1, Hp2.
  have o1 := H1 _ (restrict_admissible beta hps) Hp1.
  have o2 := H2 _ (restrict_admissible (c_not beta) hps) Hp2.
  have e := run_if_mass beta s1 s2 (formula_assertion gamma) hps.
  cbn -[measure_of] in o1, o2, e |- *. lra.
Qed.

Lemma hoare_valid_if_ge (eta1 eta2 : PFormula) beta gamma y1 y2 s1 s2 :
  hoare_valid eta1 s1 (PFLe (PProb gamma) (PVar y1)) ->
  hoare_valid eta2 s2 (PFLe (PProb gamma) (PVar y2)) ->
  hoare_valid (if_precondition eta1 eta2 beta) (CIf beta s1 s2)
    (PFLe (PProb gamma) (PAdd (PVar y1) (PVar y2))).
Proof.
  intros H1 H2 ps hps Hpre.
  apply psatisfies_and in Hpre; destruct Hpre as [Hp1 Hp2].
  apply condition_pformula_correct in Hp1, Hp2.
  have o1 := H1 _ (restrict_admissible beta hps) Hp1.
  have o2 := H2 _ (restrict_admissible (c_not beta) hps) Hp2.
  have e := run_if_mass beta s1 s2 (formula_assertion gamma) hps.
  cbn -[measure_of] in o1, o2, e |- *. lra.
Qed.

(** A restricted state is concentrated on its restricting formula. *)
Lemma restrict_almost_sure ps (gamma : CFormula D) :
  psatisfies (pstate_restrict ps gamma) (p_almost_sure gamma).
Proof.
  apply psatisfies_almost_sure. rewrite !restrict_measure_of.
  apply measure_extensional. intros v. split; [intros [_ H]; split; [apply satisfies_true|exact H] | tauto].
Qed.

Lemma sum_pre_split (eta1 eta2 : PFormula) gamma1 gamma2 ps :
  psatisfies ps (sum_precondition eta1 eta2 gamma1 gamma2) ->
  psatisfies (pstate_restrict ps gamma1) (p_and eta1 (p_almost_sure gamma1)) /\
  psatisfies (pstate_restrict ps gamma2) (p_and eta2 (p_almost_sure gamma2)) /\
  psatisfies ps (p_almost_sure (c_or gamma1 gamma2)).
Proof.
  intros H. apply psatisfies_and in H; destruct H as [H HS].
  apply psatisfies_and in H; destruct H as [H1 H2].
  apply condition_pformula_correct in H1, H2.
  split; [|split; [|exact HS]]; apply psatisfies_and; split;
    try assumption; apply restrict_almost_sure.
Qed.

Lemma hoare_valid_sum_le (eta1 eta2 : PFormula) gamma1 gamma2 gamma y1 y2 s :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_valid (p_and eta1 (p_almost_sure gamma1)) s (PFLe (PVar y1) (PProb gamma)) ->
  hoare_valid (p_and eta2 (p_almost_sure gamma2)) s (PFLe (PVar y2) (PProb gamma)) ->
  hoare_valid (sum_precondition eta1 eta2 gamma1 gamma2) s
    (PFLe (PAdd (PVar y1) (PVar y2)) (PProb gamma)).
Proof.
  intros hdisj H1 H2 ps hps Hpre.
  destruct (sum_pre_split Hpre) as [Hp1 [Hp2 HS]].
  have o1 := H1 _ (restrict_admissible gamma1 hps) Hp1.
  have o2 := H2 _ (restrict_admissible gamma2 hps) Hp2.
  have e := run_split_mass s (formula_assertion gamma) hps hdisj HS.
  cbn -[measure_of] in o1, o2, e |- *. lra.
Qed.

Lemma hoare_valid_sum_ge (eta1 eta2 : PFormula) gamma1 gamma2 gamma y1 y2 s :
  cformula_valid (c_not (c_and gamma1 gamma2)) ->
  hoare_valid (p_and eta1 (p_almost_sure gamma1)) s (PFLe (PProb gamma) (PVar y1)) ->
  hoare_valid (p_and eta2 (p_almost_sure gamma2)) s (PFLe (PProb gamma) (PVar y2)) ->
  hoare_valid (sum_precondition eta1 eta2 gamma1 gamma2) s
    (PFLe (PProb gamma) (PAdd (PVar y1) (PVar y2))).
Proof.
  intros hdisj H1 H2 ps hps Hpre.
  destruct (sum_pre_split Hpre) as [Hp1 [Hp2 HS]].
  have o1 := H1 _ (restrict_admissible gamma1 hps) Hp1.
  have o2 := H2 _ (restrict_admissible gamma2 hps) Hp2.
  have e := run_split_mass s (formula_assertion gamma) hps hdisj HS.
  cbn -[measure_of] in o1, o2, e |- *. lra.
Qed.

End SplitRules.
