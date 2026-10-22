(** Soundness of [W^UB_{m,k}] (App. C, Lemma 16).

    The proof works pointwise on starting valuations, using the kernel
    semantics.  From a valuation in [beta /\ gamma_i], the probability of
    leaving the loop within [n] iterations in [gamma] is at most [x_i]; this
    is an induction on [n] using the one-step bounds of the body triples, the
    covering condition, and the pre-fixed-point inequalities.  Integrating
    over a measure concentrated on [beta /\ gamma_k] gives the rule.  The
    side condition [0 <= x_i] (missing from the old PHLTest formalization) is
    used in the base case and to multiply the transition bounds. *)
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
  Soundness.LowerCertificate Soundness.IntegralBounds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section WhileUpper.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

Variables (m k : nat) (beta gamma : CFormula D) (body : Cmd D).
Variables (regions : nat -> CFormula D) (x exits : nat -> R) (transitions : nat -> nat -> R).
Hypothesis Hk : (k < m)%coq_nat.
Hypothesis Hcover : while_regions_cover m beta regions.
Hypothesis Hbody : forall i, (i < m)%coq_nat ->
  hoare_valid (p_concentrated_unit (regions i)) body
    (while_body_post_upper m regions (transitions i) beta gamma (exits i)).
Hypothesis Hsol : while_upper_solution m x transitions exits.

Local Notation K := (CommandSemantics.denote body).
Local Notation Gam := (formula_assertion gamma : set Valuation).
Local Notation Ex := (formula_assertion (c_and (c_not beta) gamma) : set Valuation).
Local Notation Rg j := (formula_assertion (regions j) : set Valuation).

Lemma x_nonneg i : (i < m)%coq_nat -> (0 <= x i)%R.
Proof. by move=> hi; have [_ [h _]] := Hsol hi; apply/RleP. Qed.

Lemma x_nonneg' i : (i < m)%N -> (0 <= x i)%R.
Proof. by move/ssrnat.ltP; exact: x_nonneg. Qed.

(** One-step bounds from the body triples, read at a point of [gamma_i]. *)
Lemma upper_step i w : (i < m)%coq_nat -> satisfies w (regions i) ->
  K w Ex <= (exits i)%:E /\
  (forall j, (j < m)%N -> K w (Rg j) <= (transitions i j)%:E).
Proof.
move=> hi hw.
have H := body_at_point (fun _ => 0%R) (Hbody hi) hw.
move/psatisfies_and: H => [/finite_p_and_spec Hj He].
split.
- by rewrite -kernel_massE lee_fin; apply/RleP; exact: He.
- move=> j hj; rewrite -kernel_massE lee_fin; apply/RleP.
  by have := Hj j (elimT ssrnat.ltP hj).
Qed.

(** Pointwise bound on the integrand used in the induction step. *)
Definition upper_bound_fun (z : Valuation) : \bar real :=
  (\1_Ex z)%:E + fsum_e m (fun j => (x j)%:E * (\1_(Rg j) z)%:E).

Lemma upper_bound_fun_ge0 z : 0 <= upper_bound_fun z.
Proof.
apply: adde_ge0; first by rewrite lee_fin.
apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?x_nonneg'//.
Qed.

Lemma upper_bound_fun_integral w i : (i < m)%coq_nat -> satisfies w (regions i) ->
  \int[K w]_z upper_bound_fun z <= (x i)%:E.
Proof.
move=> hi hw; have [hE hT] := upper_step hi hw.
rewrite /upper_bound_fun (ge0_integralD _ measurableT); cbv beta;
  try (by move=> z _; rewrite lee_fin);
  try (by move=> z _; apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?x_nonneg');
  try exact: (@measurable_from_valuation D _ _ _).
rewrite (@integral_indic _ _ _ (K w) setT measurableT Ex (all_measurable _)) setIT.
rewrite (@integral_fsum_indic D (K w) m x (fun j => Rg j) (fun j hj => x_nonneg' hj)).
apply: (@le_trans _ _ ((exits i)%:E +
          fsum_e m (fun j => (x j)%:E * (transitions i j)%:E))).
  apply: leeD; first exact: hE.
  apply: fsum_e_le => j hj; apply: lee_wpmul2l; first by rewrite lee_fin x_nonneg'.
  exact: hT.
have -> : fsum_e m (fun j => (x j)%:E * (transitions i j)%:E) =
          (finite_r_sum m (fun j => transitions i j * x j))%:E.
  rewrite -fsum_e_EFin; congr fsum_e; apply: funext => j; by rewrite -EFinM mulrC.
rewrite -EFinD lee_fin.
have [h _] := Hsol hi.
move/RleP: h => h.
by rewrite addrC.
Qed.

(** Probability of exiting into [gamma] within [n] iterations. *)
Lemma upper_approx n : forall w i, (i < m)%coq_nat ->
  satisfies w beta -> satisfies w (regions i) ->
  loop_approx beta K n w Gam <= (x i)%:E.
Proof.
elim: n => [|n IH] w i hi hb hw;
  have hbw : cformula_eval_bool beta w = true by exact/cformula_eval_bool_spec.
- by rewrite loop_approx_guard0 // lee_fin x_nonneg.
- rewrite loop_approx_enter //.
  apply: le_trans (upper_bound_fun_integral hi hw).
  apply: ge0_le_integral => //;
    try exact: (@measurable_from_valuation D _ _ _);
    try (by move=> z _; exact: measure_ge0);
    try (by move=> z _; exact: upper_bound_fun_ge0).
  move=> z _.
  destruct (cformula_eval_bool beta z) eqn:hz.
  + have hbz : satisfies z beta by exact/cformula_eval_bool_spec.
    have := Hcover hbz; move/satisfies_finite_c_or => [j [hj hjz]].
    apply: le_trans (IH z j hj hbz hjz) _.
    rewrite /upper_bound_fun fsum_e_indicE.
    apply: (le_trans _ (leeDr _ _)); last by rewrite lee_fin.
    rewrite lee_fin.
    have -> : x j = (x j * (\1_(Rg j) z : real))%R.
      by rewrite indicE mem_set ?mulr1.
    apply/RleP; apply: (@finite_r_sum_term m (fun j' => x j' * (\1_(Rg j') z : real))%R j); last exact: hj.
    move=> j' hj'; apply/RleP; apply: mulr_ge0; first exact: x_nonneg hj'.
    by rewrite indicE; case: (_ \in _).
  + rewrite loop_approx_exit // diracE /upper_bound_fun.
    apply: (le_trans _ (leeDl _ _)); last first.
      by apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?x_nonneg'.
    rewrite indicE lee_fin.
    case: (boolP (z \in Gam)) => hg //=.
    have hEx : Ex z.
      apply/satisfies_and; split; first exact/cformula_eval_bool_false.
      exact: set_mem hg.
    by rewrite mem_set.
Qed.

Lemma upper_loop w i : (i < m)%coq_nat -> satisfies w beta -> satisfies w (regions i) ->
  CommandSemantics.denote (CWhile beta body) w Gam <= (x i)%:E.
Proof.
move=> hi hb hw; apply: loop_le_of_approx => n; exact: upper_approx.
Qed.

End WhileUpper.

Section WhileUpperRule.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).

Lemma hoare_valid_while_upper (m k : nat) (beta gamma : CFormula D) (body : Cmd D)
    (regions : nat -> CFormula D) (x exits : nat -> R) (transitions : nat -> nat -> R)
    (y : ProbLogicVar) :
  (k < m)%coq_nat ->
  while_regions_cover m beta regions ->
  (forall i, (i < m)%coq_nat ->
    hoare_valid (p_concentrated_unit (regions i)) body
      (while_body_post_upper m regions (transitions i) beta gamma (exits i))) ->
  while_upper_solution m x transitions exits ->
  hoare_valid
    (p_and (p_almost_sure (c_and beta (regions k))) (PFLe (PProb c_true) (PVar y)))
    (CWhile beta body)
    (PFLe (PProb gamma) (PMul (PConst (x k)) (PVar y))).
Proof.
move=> Hk Hcover Hbody Hsol ps hps Hpre.
move/psatisfies_and: Hpre => [/psatisfies_almost_sure HG Hy].
rewrite /= in Hy.
set mu := pstate_measure ps.
set G := formula_assertion (c_and beta (regions k)) : set Valuation.
have hnull_r := measure_of_complement_null hps HG.
have hnull : mu (~` G) = 0.
  rewrite -(measure_ofE _ hps).
  have -> : (~` G) = (fun v => ~ satisfies v (c_and beta (regions k))) by [].
  by rewrite hnull_r.
have xk0 : (0 <= x k)%R by have [_ [h _]] := Hsol k Hk; apply/RleP.
have f0 v : 0 <= CommandSemantics.denote (CWhile beta body) v
                  (formula_assertion gamma : set Valuation) by exact: measure_ge0.
have h1 v : G v -> CommandSemantics.denote (CWhile beta body) v
                  (formula_assertion gamma : set Valuation) <= (x k)%:E.
  move=> /satisfies_and [hb hr].
  exact: (upper_loop Hcover Hbody Hsol Hk hb hr).
have h2 v : ~ G v -> CommandSemantics.denote (CWhile beta body) v
                  (formula_assertion gamma : set Valuation) <= 1%:E.
  by move=> _; exact: kernel_le1.
have hint := @integral_le_split D mu _ G (x k) 1%R xk0 ler01 f0 h1 h2.
rewrite hnull mule0 adde0 -(measure_ofE _ hps) -EFinM in hint.
have hout : (measure_of (pstate_measure (run (CWhile beta body) ps))
               (formula_assertion gamma) <= x k * measure_of mu G)%R.
  have hr := run_admissible (CWhile beta body) hps.
  rewrite -lee_fin measure_ofE //.
rewrite /= -/mu.
move/RleP: hout => hout.
have hG1 : measure_of mu G = measure_of mu (formula_assertion c_true) by exact: HG.
rewrite hG1 in hout.
apply/RleP; apply: (le_trans (introT RleP hout)).
apply/RleP; apply: Rmult_le_compat_l; [exact/RleP | exact: Hy].
Qed.

End WhileUpperRule.
