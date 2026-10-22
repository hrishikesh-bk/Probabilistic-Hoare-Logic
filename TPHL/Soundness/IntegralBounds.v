(** Bounding integrals over valuations by finitely many indicator pieces;
    used by the while rules. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration PHL.
Require Import Soundness.LoopFacts Soundness.LowerCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section IntegralBounds.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

Lemma indicP (A : set Valuation) v :
  (\1_A v : real) = if pselect (A v) then 1%R else 0%R.
Proof. by rewrite indicE; case: pselect => h; [rewrite mem_set | rewrite memNset]. Qed.

Lemma indic_ge0E (A : set Valuation) v : 0 <= (\1_A v : real)%:E.
Proof. by rewrite lee_fin. Qed.

(** [int f <= a mu(G) + b mu(~G)] when [f <= a] on [G] and [f <= b] off [G]. *)
Lemma integral_le_split (mu : carrier) (f : Valuation -> \bar real)
    (G : set Valuation) (a b : real) :
  (0 <= a)%R -> (0 <= b)%R -> (forall v, 0 <= f v) ->
  (forall v, G v -> f v <= a%:E) -> (forall v, ~ G v -> f v <= b%:E) ->
  \int[mu]_v f v <= a%:E * mu G + b%:E * mu (~` G).
Proof.
move=> a0 b0 f0 hG hN.
apply: (@le_trans _ _ (\int[mu]_v (a%:E * (\1_G v)%:E + b%:E * (\1_(~` G) v)%:E))).
  apply: ge0_le_integral => //;
    try exact: (@measurable_from_valuation D _ _ _);
    try (by move=> v _; exact: f0);
    try (by move=> v _; apply: adde_ge0; apply: mule_ge0; rewrite lee_fin).
  move=> v _; rewrite !indicP.
  case: pselect => hv; case: pselect => hv' /=.
  - by exfalso; exact: hv' hv.
  - by rewrite mule1 mule0 adde0; exact: hG.
  - by rewrite mule0 mule1 add0e; exact: hN.
  - by exfalso; exact: hv' hv.
rewrite (ge0_integralD _ measurableT); cbv beta;
  try (by move=> v _; apply: mule_ge0; rewrite lee_fin);
  try exact: (@measurable_from_valuation D _ _ _).
by rewrite !integral_scaled_indic.
Qed.

(** [a mu(G) <= int f] when [a <= f] on [G]. *)
Lemma integral_ge_split (mu : carrier) (f : Valuation -> \bar real)
    (G : set Valuation) (a : real) :
  (0 <= a)%R -> (forall v, 0 <= f v) -> (forall v, G v -> a%:E <= f v) ->
  a%:E * mu G <= \int[mu]_v f v.
Proof.
move=> a0 f0 hG.
rewrite -integral_scaled_indic//.
apply: ge0_le_integral => //;
  try exact: (@measurable_from_valuation D _ _ _);
  try (by move=> v _; exact: f0);
  try (by move=> v _; apply: mule_ge0; rewrite lee_fin).
move=> v _; rewrite indicP; case: pselect => hv /=.
- by rewrite mule1; exact: hG.
- by rewrite mule0; exact: f0.
Qed.

(** Finite weighted sums of indicators at a point, in [R]. *)
Lemma fsum_e_indicE m (c : nat -> real) (A : nat -> set Valuation) v :
  fsum_e m (fun j => (c j)%:E * (\1_(A j) v)%:E) =
  (finite_r_sum m (fun j => c j * (\1_(A j) v : real)))%:E.
Proof.
rewrite -fsum_e_EFin; congr fsum_e; apply: funext => j; by rewrite EFinM.
Qed.

End IntegralBounds.
