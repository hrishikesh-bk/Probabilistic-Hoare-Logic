(** Soundness of [W^LB_{m,k}] (App. C, Lemma 17).

    Let [L(v)] be the probability that the loop, started in [v], exits in
    [gamma], and let [l_i] be the infimum of [L] over region [gamma_i] (or [1]
    if the region is empty).  The loop's fixed-point equation and the
    one-step lower bounds of the body triples make [l] a pre-fixed point of
    [Q(z)_i = sum_j q_ij z_j + q_i], where [q = max(r, 0)].  The certificate
    [x] is a post-fixed point, and the progress condition makes the system
    transient, so [x <= l] by [post_fixed_below_pre_fixed]
    (LowerCertificate.v).  Integrating over a measure concentrated on
    [gamma_k] gives the rule.

    Unlike App. C, row bounds [sum_j q_ij + q_i <= 1] are only derived for
    nonempty regions: for an empty region the body triple is vacuous. *)
From Stdlib Require Import Reals Lra Lia.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration PHL.
Require Import Soundness.StateFacts Soundness.CommandFacts Soundness.AssertionFacts
  Soundness.TransformerAssertions Soundness.SplitRules Soundness.LoopFacts
  Soundness.LowerCertificate Soundness.IntegralBounds Soundness.LowerFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** ** The lower-bound argument *)

Unset Implicit Arguments.

Section WhileLower.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

Variables (m k : nat) (beta gamma : CFormula D) (body : Cmd D).
Variables (regions : nat -> CFormula D) (x exits : nat -> R) (transitions : nat -> nat -> R).
Hypothesis Hk : (k < m)%coq_nat.
Hypothesis Hguard : while_regions_in_guard m beta regions.
Hypothesis Hdisj : while_regions_disjoint m regions.
Hypothesis Hprog : while_progress m transitions exits.
Hypothesis Hbody : forall i, (i < m)%coq_nat ->
  hoare_valid (p_concentrated_unit (regions i)) body
    (while_body_post_lower m regions (transitions i) beta gamma (exits i)).
Hypothesis Hsol : while_lower_solution m x transitions exits.

Local Notation K := (CommandSemantics.denote body).
Local Notation W := (CommandSemantics.denote (CWhile beta body)).
Local Notation Gam := (formula_assertion gamma : set Valuation).
Local Notation Ex := (formula_assertion (c_and (c_not beta) gamma) : set Valuation).
Local Notation Rg j := (formula_assertion (regions j) : set Valuation).

(** Loop exit probability from a valuation, as a real. *)
Definition L (z : Valuation) : R := fine (W z Gam).

Lemma LE z : (L z)%:E = W z Gam.
Proof.
apply: fineK; rewrite ge0_fin_numE ?measure_ge0//.
exact: le_lt_trans (kernel_le1 _ _ _) (ltry 1).
Qed.

Lemma L_ge0 z : (0 <= L z)%R.
Proof. by rewrite -lee_fin LE measure_ge0. Qed.

Definition live i : Prop := exists w : Valuation, satisfies w (regions i).

Definition lval i : R :=
  if pselect (live i) then inf [set L w | w in Rg i] else 1%R.

Lemma lval_le i w : satisfies w (regions i) -> (lval i <= L w)%R.
Proof.
move=> hw; rewrite /lval; destruct (pselect (live i)) as [hl | n]; last by exfalso; apply: n; exists w.
apply: ge_inf; last by exists w.
by exists 0%R => _ [z _ <-]; exact: L_ge0.
Qed.

Lemma lval_ge0 i : (0 <= lval i)%R.
Proof.
rewrite /lval; destruct (pselect (live i)) as [[w hw] | hn]; last exact: ler01.
apply: lb_le_inf; first by exists (L w), w.
by move=> _ [z _ <-]; exact: L_ge0.
Qed.

Lemma lval_glb i c : live i -> (forall w, satisfies w (regions i) -> (c <= L w)%R) ->
  (c <= lval i)%R.
Proof.
move=> [w hw] hc; rewrite /lval; destruct (pselect (live i)) as [hl | n]; last by exfalso; apply: n; exists w.
apply: lb_le_inf; first by exists (L w), w.
by move=> _ [z hz <-]; exact: hc.
Qed.

(** Nonnegative parts of the certificate. *)
Definition q i j : R := Rmax (transitions i j) 0.
Definition qe i : R := Rmax (exits i) 0.

Local Notation kmass w A := (measure_of (K w) A).

(** One-step lower bounds from the body triples at a point of [gamma_i]. *)
Lemma lower_step i w : (i < m)%coq_nat -> satisfies w (regions i) ->
  Rle (exits i) (kmass w Ex) /\
  (forall j, (j < m)%coq_nat -> Rle (transitions i j) (kmass w (Rg j))).
Proof.
move=> hi hw.
have H := body_at_point (fun _ => 0%R) (Hbody i hi) hw.
move/psatisfies_and: H => [/finite_p_and_spec Hj He].
by split; [exact: He | move=> j hj; exact: Hj j hj].
Qed.

Lemma q_le i w j : (i < m)%coq_nat -> satisfies w (regions i) -> (j < m)%coq_nat ->
  Rle (q i j) (kmass w (Rg j)).
Proof.
move=> hi hw hj; apply: Rmax_lub; first exact: (proj2 (lower_step i w hi hw) j hj).
exact: measure_nonnegative.
Qed.

Lemma qe_le i w : (i < m)%coq_nat -> satisfies w (regions i) -> Rle (qe i) (kmass w Ex).
Proof.
move=> hi hw; apply: Rmax_lub; first exact: (proj1 (lower_step i w hi hw)).
exact: measure_nonnegative.
Qed.

Lemma regions_disjoint i j v : (i < m)%coq_nat -> (j < m)%coq_nat -> i <> j ->
  ~ (satisfies v (regions i) /\ satisfies v (regions j)).
Proof.
move=> hi hj hne [hvi hvj].
destruct (Nat.lt_total i j) as [hlt|[heq|hgt]].
- by apply: (Hdisj j i hj hlt v); apply/satisfies_and; split.
- by [].
- by apply: (Hdisj i j hi hgt v); apply/satisfies_and; split.
Qed.

Lemma region_guard i v : (i < m)%coq_nat -> satisfies v (regions i) -> satisfies v beta.
Proof. by move=> hi hv; exact: (Hguard i hi v hv). Qed.

Lemma kernel_subprobK w : Subprob (K w).
Proof. exact: kernel_subprob. Qed.

(** Row bounds on nonempty regions. *)
Lemma lower_rows i w : (i < m)%coq_nat -> satisfies w (regions i) ->
  Rle (Rplus (finite_r_sum m (q i)) (qe i)) 1.
Proof.
move=> hi hw.
apply: (Rle_trans _ (Rplus (finite_r_sum m (fun j => kmass w (Rg j))) (kmass w Ex))).
  apply: Rplus_le_compat; last exact: qe_le.
  by apply: finite_r_sum_le => j hj; exact: q_le.
apply: (Rle_trans _ (kmass w (fun _ => True))).
  apply: (fsum_disjoint_le (K w) m (fun j => Rg j) Ex (kernel_subprobK w)).
  - move=> i' j' hi' hj' v; apply: regions_disjoint; [exact: hi' | lia | lia].
  - move=> j hj v [hRj hE].
    have [hnb _] := proj1 (satisfies_and v (c_not beta) gamma) hE.
    exact: hnb (region_guard j v hj hRj).
exact: (measure_subprobability (K w) (kernel_subprobK w)).
Qed.

(** Columns of empty regions vanish in live rows. *)
Lemma dead_columns i j : (i < m)%coq_nat -> live i -> (j < m)%coq_nat -> ~ live j ->
  q i j = 0%R.
Proof.
move=> hi [w hw] hj hdead.
have e : kmass w (Rg j) = kmass w (fun _ => False).
  by apply: measure_extensional => v; split => // hv; apply: hdead; exists v.
have hz : kmass w (Rg j) = 0%R by rewrite e measure_empty.
have := proj2 (lower_step i w hi hw) j hj; rewrite hz => hr.
by rewrite /q Rmax_right.
Qed.

Lemma lower_progress i : (i < m)%coq_nat -> live i ->
  Rlt 0 (qe i) \/ exists j, (j < i)%coq_nat /\ Rlt 0 (q i j).
Proof.
move=> hi _; case: (Hprog i hi) => [he | [j [hj hr]]].
- by left; apply: (Rlt_le_trans _ _ _ he); exact: Rmax_l.
- by right; exists j; split => //; apply: (Rlt_le_trans _ _ _ hr); exact: Rmax_l.
Qed.

Lemma x_nonneg j : (j < m)%coq_nat -> Rle 0 (x j).
Proof. by move=> hj; have [_ [h _]] := Hsol j hj. Qed.

Lemma lower_x_post i : (i < m)%coq_nat ->
  Rle (x i) (Rplus (finite_r_sum m (fun j => Rmult (q i j) (x j))) (qe i)).
Proof.
move=> hi; have [h _] := Hsol i hi.
exact: (post_fixed_nonneg_part m x (transitions i) (exits i) (x i) x_nonneg h).
Qed.

(** The integrand used in the fixed-point step. *)
Definition lower_fun (z : Valuation) : \bar real :=
  (\1_Ex z)%:E + fsum_e m (fun j => (lval j)%:E * (\1_(Rg j) z)%:E).

Lemma lower_fun_ge0 z : 0 <= lower_fun z.
Proof.
apply: adde_ge0; first by rewrite lee_fin.
apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?lval_ge0//.
Qed.

Lemma lower_fun_le z : lower_fun z <= W z Gam.
Proof.
rewrite /lower_fun fsum_e_indicE.
have hind j : (\1_(Rg j) z : real) = if pselect (Rg j z) then 1%R else 0%R by exact: indicP.
destruct (cformula_eval_bool beta z) eqn:hz.
- (* inside the guard: the exit indicator vanishes *)
  have hb : satisfies z beta by exact/cformula_eval_bool_spec.
  have -> : (\1_Ex z : real) = 0%R.
    rewrite indicP; destruct (pselect (Ex z)) as [hE|hE] => //.
    by have [hnb _] := proj1 (satisfies_and z (c_not beta) gamma) hE; exfalso; exact: hnb hb.
  rewrite add0e -LE lee_fin.
  have es : finite_r_sum m (fun j => (lval j * (\1_(Rg j) z : real))%R) =
            finite_r_sum m (fun j => Rmult (lval j)
              (match pselect (Rg j z) with left _ => R1 | right _ => R0 end)).
    by apply: finite_r_sum_ext => j _; rewrite hind; destruct (pselect (Rg j z)).
  rewrite es.
  apply/RleP; apply: (fsum_disjoint_indicator_le m (fun j => Rg j z) lval (L z)).
  + by move=> i' j' hi' hj' hP; apply: (regions_disjoint i' j' z hi' _ _ hP); lia.
  + by move=> j hj hP; apply/RleP; exact: lval_le.
  + by apply/RleP; exact: L_ge0.
- (* outside the guard: the loop stops, and no region holds *)
  have hnb : ~ satisfies z beta by exact/cformula_eval_bool_false.
  have es : finite_r_sum m (fun j => (lval j * (\1_(Rg j) z : real))%R) =
            finite_r_sum m (fun _ => 0%R).
    apply: finite_r_sum_ext => j hj; rewrite hind; destruct (pselect (Rg j z)) as [hR|hR].
    + by exfalso; exact: hnb (region_guard j z hj hR).
    + by rewrite mulr0.
  rewrite es.
  have eW : W z Gam = dirac z Gam.
    by change (loop beta K z Gam = dirac z Gam); rewrite loop_unfold hz.
  rewrite eW.
  rewrite finite_r_sum_zero adde0 diracE indicP.
  rewrite lee_fin; destruct (pselect (Ex z)) as [hE|hE].
  + have hG : Gam z by have [_ h] := proj1 (satisfies_and z (c_not beta) gamma) hE.
    by rewrite mem_set.
  + by case: (_ \in _).
Qed.

(** [l] is a pre-fixed point on live rows. *)
Lemma lower_point i w : (i < m)%coq_nat -> satisfies w (regions i) ->
  Rle (Rplus (finite_r_sum m (fun j => Rmult (q i j) (lval j))) (qe i)) (L w).
Proof.
move=> hi hw.
have hbw : cformula_eval_bool beta w = true by exact/cformula_eval_bool_spec/(region_guard i w hi hw).
have hL : (L w)%:E = \int[K w]_z W z Gam.
  rewrite LE; change (loop beta K w Gam = \int[K w]_z loop beta K z Gam).
  by rewrite loop_unfold hbw.
have hint : \int[K w]_z lower_fun z <= \int[K w]_z W z Gam.
  apply: ge0_le_integral => //;
    try exact: (@measurable_from_valuation D _ _ _);
    try (by move=> z _; exact: lower_fun_ge0).
  by move=> z _; exact: lower_fun_le.
have eint : \int[K w]_z lower_fun z =
    K w Ex + fsum_e m (fun j => (lval j)%:E * K w (Rg j)).
  rewrite /lower_fun (ge0_integralD _ measurableT); cbv beta;
    try (by move=> z _; rewrite lee_fin);
    try (by move=> z _; apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?lval_ge0);
    try exact: (@measurable_from_valuation D _ _ _).
  rewrite (@integral_indic _ _ _ (K w) setT measurableT Ex (all_measurable _)) setIT.
  by rewrite (@integral_fsum_indic D (K w) m lval (fun j => Rg j) (fun j _ => lval_ge0 j)).
rewrite -hL eint in hint.
have efs : fsum_e m (fun j => (lval j)%:E * K w (Rg j)) =
          (finite_r_sum m (fun j => Rmult (lval j) (kmass w (Rg j))))%:E.
  rewrite -fsum_e_EFin; congr fsum_e; apply: funext => j; by rewrite EFinM kernel_massE.
rewrite efs in hint.
rewrite -kernel_massE -EFinD lee_fin in hint; move/RleP: hint => hint.
apply: (Rle_trans _ _ _ _ hint).
rewrite Rplus_comm; apply: Rplus_le_compat; first exact: qe_le.
apply: finite_r_sum_le => j hj.
rewrite Rmult_comm; apply: Rmult_le_compat_l; first by apply/RleP; exact: lval_ge0.
exact: q_le.
Qed.

Lemma lower_pre i : (i < m)%coq_nat -> live i ->
  Rle (Rplus (finite_r_sum m (fun j => Rmult (q i j) (lval j))) (qe i)) (lval i).
Proof.
move=> hi hl; apply/RleP; apply: lval_glb => // w hw.
by apply/RleP; exact: lower_point.
Qed.

(** The certificate is below the exit probabilities. *)
Lemma lower_below i : (i < m)%coq_nat -> live i -> Rle (x i) (lval i).
Proof.
apply: (post_fixed_below_pre_fixed m live q qe x lval).
- by move=> i' j'; exact: Rmax_r.
- by move=> i'; exact: Rmax_r.
- by move=> i' hi' [w hw]; exact: (lower_rows i' w hi' hw).
- exact: dead_columns.
- exact: lower_progress.
- by move=> i' hi' _; exact: lower_x_post.
- exact: lower_pre.
Qed.

Lemma lower_loop v : satisfies v (regions k) -> (x k)%:E <= W v Gam.
Proof.
move=> hv; rewrite -LE lee_fin; apply/RleP.
apply: (Rle_trans _ (lval k)); first by apply: lower_below => //; exists v.
by apply/RleP; exact: lval_le.
Qed.

End WhileLower.

Set Implicit Arguments.

Section WhileLowerRule.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).

Lemma hoare_valid_while_lower (m k : nat) (beta gamma : CFormula D) (body : Cmd D)
    (regions : nat -> CFormula D) (x exits : nat -> R) (transitions : nat -> nat -> R)
    (y : ProbLogicVar) :
  (k < m)%coq_nat ->
  while_regions_in_guard m beta regions ->
  while_regions_disjoint m regions ->
  while_progress m transitions exits ->
  (forall i, (i < m)%coq_nat ->
    hoare_valid (p_concentrated_unit (regions i)) body
      (while_body_post_lower m regions (transitions i) beta gamma (exits i))) ->
  while_lower_solution m x transitions exits ->
  hoare_valid
    (p_and (p_almost_sure (c_and beta (regions k))) (PFLe (PVar y) (PProb c_true)))
    (CWhile beta body)
    (PFLe (PMul (PConst (x k)) (PVar y)) (PProb gamma)).
Proof.
move=> Hk Hguard Hdisj Hprog Hbody Hsol ps hps Hpre.
move/psatisfies_and: Hpre => [/psatisfies_almost_sure HG Hy].
rewrite /= in Hy.
set mu := pstate_measure ps.
set Gk := formula_assertion (regions k) : set Valuation.
have xk0 : (0 <= x k)%R by have [_ [h _]] := Hsol k Hk; apply/RleP.
have f0 v : 0 <= CommandSemantics.denote (CWhile beta body) v
                  (formula_assertion gamma : set Valuation) by exact: measure_ge0.
have h1 v : Gk v -> (x k)%:E <= CommandSemantics.denote (CWhile beta body) v
                  (formula_assertion gamma : set Valuation).
  exact: (lower_loop m k beta gamma body regions x exits transitions
            Hk Hguard Hdisj Hprog Hbody Hsol v).
have hint := @integral_ge_split D mu _ Gk (x k) xk0 f0 h1.
have hr := run_admissible (CWhile beta body) hps.
rewrite -(measure_ofE _ hps) -EFinM -transform_event -/(transform_cmd _ _) in hint.
change (transform_cmd (CWhile beta body) mu) with (pstate_measure (run (CWhile beta body) ps)) in hint.
rewrite -(measure_ofE _ hr) lee_fin in hint; move/RleP: hint => hint.
rewrite /= -/mu.
apply: (Rle_trans _ (x k * measure_of mu Gk)%R); last exact: hint.
(* mu(gamma_k) >= mu(beta /\ gamma_k) = mu(tt) >= y *)
have hGk : Rle (measure_of mu (formula_assertion c_true)) (measure_of mu Gk).
  rewrite -HG; apply: measure_of_monotone => // v.
  by move=> hv'; have [_ h] := proj1 (satisfies_and v beta (regions k)) hv'.
apply: Rmult_le_compat_l; first exact/RleP.
exact: (Rle_trans _ _ _ Hy hGk).
Qed.

End WhileLowerRule.
