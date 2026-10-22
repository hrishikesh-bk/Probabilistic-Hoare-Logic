(** Soundness of [W~] (App. C, Lemma 18): if all mass satisfies
    [~beta /\ gamma], the loop is never entered and the output is the
    input. *)
From Stdlib Require Import Reals Lra.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration PHL.
Require Import Soundness.StateFacts Soundness.CommandFacts Soundness.AssertionFacts
  Soundness.TransformerAssertions Soundness.SplitRules Soundness.LoopFacts
  Soundness.IntegralBounds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section WhileNonentry.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

(** If the input is concentrated on a set [G] where the guard fails, the
    loop exits at once: every event containing [G] gets mass [mu(G)]. *)
Lemma while_nonentry_out (beta : CFormula D) body (mu : carrier) (G A : set Valuation) :
  (forall v, G v -> cformula_eval_bool beta v = false) -> mu (~` G) = 0 ->
  (forall v, G v -> A v) ->
  transform (CommandSemantics.denote (CWhile beta body)) mu A = mu G.
Proof.
move=> hG hnull hGA.
have f0 v : 0 <= CommandSemantics.denote (CWhile beta body) v A by exact: measure_ge0.
have hexit v : G v -> CommandSemantics.denote (CWhile beta body) v A = 1.
  move=> hv; change (loop beta (CommandSemantics.denote body) v A = 1).
  by rewrite loop_unfold hG // diracE mem_set //; exact: hGA.
rewrite transform_event; apply/le_anti/andP; split.
- have h1 : forall v, G v -> CommandSemantics.denote (CWhile beta body) v A <= 1%:E.
    by move=> v hv; rewrite hexit.
  have h2 : forall v, ~ G v -> CommandSemantics.denote (CWhile beta body) v A <= 1%:E.
    by move=> v _; exact: kernel_le1.
  apply: (le_trans (@integral_le_split _ mu _ G 1%R 1%R ler01 ler01 f0 h1 h2)).
  by rewrite hnull mul1e mule0 adde0.
- rewrite -[X in X <= _]mul1e.
  by apply: integral_ge_split => // v hv; rewrite hexit.
Qed.

End WhileNonentry.

Section WhileNotRule.
Context {D : Domain}.
Local Open Scope R_scope.

Lemma hoare_valid_while_not (beta gamma : CFormula D) body y :
  hoare_valid
    (p_and (p_almost_sure (c_and (c_not beta) gamma)) (p_eq (PProb c_true) (PVar y)))
    (CWhile beta body)
    (p_and (p_eq (PProb gamma) (PProb c_true)) (p_eq (PProb c_true) (PVar y))).
Proof.
  intros ps hps Hpre.
  apply psatisfies_and in Hpre; destruct Hpre as [HG Hy].
  apply psatisfies_almost_sure in HG. apply psatisfies_eq in Hy. cbn in Hy.
  set (G := formula_assertion (c_and (c_not beta) gamma)).
  set (mu := pstate_measure ps).
  have hnull_r : measure_of mu (fun v => ~ satisfies v (c_and (c_not beta) gamma)) = 0
    := measure_of_complement_null hps HG.
  have hnull : mu (~` (G : set (Valuation (D := D)))) = 0%E.
  { rewrite -(measure_ofE _ hps). change (measure_of mu (fun v => ~ satisfies v (c_and (c_not beta) gamma)))%:E with
      ((measure_of mu (fun v => ~ satisfies v (c_and (c_not beta) gamma)))%:E).
    by rewrite hnull_r. }
  have hguard v : G v -> cformula_eval_bool beta v = false.
  { intros hv. apply cformula_eval_bool_false.
    apply satisfies_and in hv. exact (proj1 hv). }
  have hout A : (forall v, G v -> A v) ->
      measure_of (pstate_measure (run (CWhile beta body) ps)) A = measure_of mu G.
  { intros hA. apply EFin_inj. have hr := run_admissible (CWhile beta body) hps.
    rewrite !measure_ofE //.
    exact: (while_nonentry_out body hguard hnull hA). }
  have hGg : forall v, G v -> formula_assertion gamma v.
  { intros v hv. apply satisfies_and in hv. exact (proj2 hv). }
  have hGt : forall v, G v -> formula_assertion (D := D) c_true v.
  { intros v _. apply satisfies_true. }
  apply psatisfies_and. split; apply psatisfies_eq; cbn -[measure_of].
  - rewrite (hout _ hGg) (hout _ hGt). reflexivity.
  - rewrite (hout _ hGt). rewrite -Hy. exact HG.
Qed.

End WhileNotRule.
