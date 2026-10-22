(** Loop kernels (series of exits, approximations, unfolding, leastness),
    adapted from CPHL's Soundness/LoopFacts.v, together with the two tools the
    while rules need: reading a body triple at a single starting valuation,
    and integrating finite weighted sums of indicators. *)
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
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section LoopKernels.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Notation Kernel := (@Kernel D).
Local Notation loop := (@loop D).
Local Notation loop_exit := (@loop_exit D).
Local Notation loop_approx := (@loop_approx D).
Implicit Types (v : Valuation) (A : set Valuation).

Lemma loop_event g (k : Kernel) v A : loop g k v A = \sum_(n <oo) loop_exit g k n v A.
Proof. reflexivity. Qed.

Lemma loop_approx_cvg g (k : Kernel) v A :
  (fun n => loop_approx g k n v A) @ \oo --> loop g k v A.
Proof.
rewrite loop_event.
have -> : (fun n => loop_approx g k n v A) =
    (fun n => \sum_(0 <= i < n.+1) loop_exit g k i v A).
  by apply/funext => n; rewrite loop_approx_sum ?big_mkord//; exact: all_measurable.
have hc := is_cvg_ereal_nneg_natsum (m:=0%N)
  (fun i _ => measure_ge0 (loop_exit g k i v) A).
rewrite -cvg_shiftS in hc; exact: hc.
Qed.

(** One unfolding of the loop: the fixed-point equation of [while]. *)
Lemma loop_unfold g (k : Kernel) v A :
  loop g k v A = if cformula_eval_bool g v
    then \int[k v]_w loop g k w A else dirac v A.
Proof.
have mA : measurable A by exact: all_measurable.
rewrite loop_event (nneseries_split 0%N 1%N)// add0n big_nat1.
rewrite -(@nneseries_addn real (fun n => loop_exit g k n v A) 1%N)//.
under eq_eseriesr do rewrite addn1 loop_exitS.
rewrite loop_exit0; case hg: (cformula_eval_bool g v).
- rewrite add0e; under [RHS]eq_integral do rewrite loop_event.
  rewrite integral_nneseries//; by move=> n; exact: measurable_kernel.
- by rewrite eseries0// adde0.
Qed.

(** Approximations of a state that fails the guard are point masses. *)
Lemma loop_approx_exit g (k : Kernel) n v A :
  cformula_eval_bool g v = false -> loop_approx g k n v A = dirac v A.
Proof.
move=> hg; case: n => [|n].
- by rewrite /loop_approx loop_exit0 hg.
- by rewrite loop_approxS hg.
Qed.

Lemma loop_approx_enter g (k : Kernel) n v A :
  cformula_eval_bool g v = true ->
  loop_approx g k n.+1 v A = \int[k v]_w loop_approx g k n w A.
Proof. by move=> hg; rewrite loop_approxS hg. Qed.

Lemma loop_approx_guard0 g (k : Kernel) v A :
  cformula_eval_bool g v = true -> loop_approx g k 0 v A = 0.
Proof. by move=> hg; rewrite /loop_approx loop_exit0 hg. Qed.

(** A bound on every approximation bounds the loop. *)
Lemma loop_le_of_approx g (k : Kernel) v A (c : \bar real) :
  (forall n, loop_approx g k n v A <= c) -> loop g k v A <= c.
Proof.
move=> h; apply (cvge_to_le (@loop_approx_cvg g k v A)).
by apply: nearW => n; exact: h.
Qed.

Lemma kernel_le1 (k : Kernel) v A : k v A <= 1.
Proof.
apply: le_trans (sprob_kernel_le1 k v).
by apply: le_measure; rewrite ?inE; [exact: all_measurable | exact: measurableT | ].
Qed.

Lemma kernel_subprob (k : Kernel) v : ConcreteMeasure.Subprob (k v).
Proof. exact: sprob_kernel_le1. Qed.

End LoopKernels.

(** ** Finite weighted sums of indicators *)

Section FiniteSums.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

Fixpoint fsum_e (m : nat) (f : nat -> \bar real) : \bar real :=
  match m with
  | O => 0
  | S m' => fsum_e m' f + f m'
  end.

Lemma fsum_e_EFin m (f : nat -> real) :
  fsum_e m (fun j => (f j)%:E) = (finite_r_sum m f)%:E.
Proof. by elim: m => [|m IH] //=; rewrite IH EFinD. Qed.

Lemma fsum_e_ge0 m (f : nat -> \bar real) :
  (forall j, (j < m)%N -> 0 <= f j) -> 0 <= fsum_e m f.
Proof.
elim: m => [|m IH] h //=; apply: adde_ge0.
- by apply: IH => j hj; apply: h; exact: ltnW.
- exact: h.
Qed.

Lemma fsum_e_le m (f g : nat -> \bar real) :
  (forall j, (j < m)%N -> f j <= g j) -> fsum_e m f <= fsum_e m g.
Proof.
elim: m => [|m IH] h //=; apply: leeD.
- by apply: IH => j hj; apply: h; exact: ltnW.
- exact: h.
Qed.

Lemma integral_scaled_indic (mu : carrier) (c : real) (A : set Valuation) :
  (0 <= c)%R -> \int[mu]_v (c%:E * (\1_A v)%:E) = c%:E * mu A.
Proof.
move=> c0.
have f0 : forall v, [set: Valuation] v -> 0 <= (\1_A v : real)%:E.
  by move=> v _; rewrite lee_fin.
have mf : measurable_fun [set: Valuation] (fun v : Valuation => (\1_A v : real)%:E).
  exact: (@measurable_from_valuation D _ _ _).
rewrite (ge0_integralZl_EFin mu measurableT f0 mf c0); congr (_ * _).
by rewrite integral_indic ?setIT//; exact: all_measurable.
Qed.

Lemma integral_fsum_indic (mu : carrier) m (c : nat -> real) (A : nat -> set Valuation) :
  (forall j, (j < m)%N -> (0 <= c j)%R) ->
  \int[mu]_v fsum_e m (fun j => (c j)%:E * (\1_(A j) v)%:E) =
  fsum_e m (fun j => (c j)%:E * mu (A j)).
Proof.
elim: m => [|m IH] c0 /=.
- by rewrite integral0.
- have c0' : forall j, (j < m)%N -> (0 <= c j)%R by move=> j hj; apply: c0; exact: ltnW.
  rewrite (ge0_integralD _ measurableT); cbv beta;
    try (by move=> v _; apply: fsum_e_ge0 => j hj; apply: mule_ge0; rewrite lee_fin ?c0');
    try (by move=> v _; apply: mule_ge0; rewrite lee_fin ?c0);
    try exact: (@measurable_from_valuation D _ _ _).
  by rewrite (IH c0') integral_scaled_indic// c0.
Qed.

End FiniteSums.

(** ** Body triples at a single starting valuation *)

Section PointBody.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation Pstate := (Pstate D).
Implicit Types (v : Valuation).

Definition point_pstate (v : Valuation) (rho : ProbLogicVar -> R) : Pstate :=
  {| pstate_measure := dirac v; pstate_prob_logic_values := rho |}.

Definition kernel_pstate (s : Cmd D) (v : Valuation) (rho : ProbLogicVar -> R) : Pstate :=
  {| pstate_measure := CommandSemantics.denote s v; pstate_prob_logic_values := rho |}.

Lemma point_admissible v rho : pstate_admissible (point_pstate v rho).
Proof. exact: ConcreteMeasure.point_subprob. Qed.

Lemma measure_of_dirac (v : Valuation) (A : Assertion D) :
  measure_of (dirac v) A = if pselect (A v) then 1%R else 0%R.
Proof.
rewrite /measure_of /ConcreteMeasure.event_mass /dirac /= indicE.
by case: pselect => h; rewrite ?(mem_set h) ?memNset.
Qed.

Lemma measure_of_dirac_in (v : Valuation) (A : Assertion D) :
  A v -> measure_of (dirac v) A = 1%R.
Proof. by move=> h; rewrite measure_of_dirac; case: pselect => // n; exfalso; exact: n h. Qed.

Lemma point_concentrated (G : CFormula D) v rho :
  satisfies v G -> psatisfies (point_pstate v rho) (p_concentrated_unit G).
Proof.
move=> hv.
have h1 : measure_of (dirac v) (formula_assertion G) = 1%R by exact: measure_of_dirac_in.
have h2 : measure_of (dirac v) (formula_assertion c_true) = 1%R.
  by apply: measure_of_dirac_in; exact: satisfies_true.
apply/psatisfies_and; split.
- by apply/psatisfies_almost_sure; rewrite /= h1 h2.
- by apply/psatisfies_eq; rewrite /= h2.
Qed.

(** The output of [s] on a point mass is [denote s v]. *)
Lemma run_point_same (s : Cmd D) v rho :
  same_masses (run s (point_pstate v rho)) (kernel_pstate s v rho).
Proof.
split => // gamma.
rewrite /measure_of /ConcreteMeasure.event_mass; congr fine.
exact: transform_point.
Qed.

Lemma body_at_point (G : CFormula D) (s : Cmd D) post v rho :
  hoare_valid (p_concentrated_unit G) s post -> satisfies v G ->
  psatisfies (kernel_pstate s v rho) post.
Proof.
move=> H hv.
apply: (proj1 (psatisfies_same_masses _ _ post (run_point_same s v rho))).
apply: H; [exact: point_admissible | exact: point_concentrated].
Qed.

(** Real bounds on kernel masses lift to extended reals. *)
Lemma kernel_massE (s : Cmd D) v (A : Assertion D) :
  (measure_of (CommandSemantics.denote s v) A)%:E = CommandSemantics.denote s v A.
Proof. apply: measure_ofE; exact: sprob_kernel_le1. Qed.

End PointBody.
