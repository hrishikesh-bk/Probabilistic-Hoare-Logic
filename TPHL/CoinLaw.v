(** Library-only coin law for [toss(bm, r)]. Adapted from the Boolean part of
    CPHL's DistributionKernels.v. The rate is an ordinary real; a rate
    outside [0,1] gives zero mass, never a fallback distribution. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions fsbigop reals topology.
From mathcomp Require Import ereal normedtype sequences numfun measure.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import bernoulli_distribution.
From mathcomp Require Import Rstruct Rstruct_topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module CoinLaw.

Definition toss_valid (p : real) := (0 <= p <= 1)%R.

Definition valid_toss (p : real) : {measure set bool -> \bar real} :=
  bernoulli_prob p.

HB.instance Definition _ p := Measure.on (valid_toss p).
HB.instance Definition _ p := Measure_isProbability.Build _ _ _
  (valid_toss p) (@probability_setT _ _ _ (bernoulli_prob p)).

(** MathComp's Bernoulli law falls back to a Dirac measure on invalid rates;
    that fallback is gated out here. *)
Definition toss (p : real) : {measure set bool -> \bar real} :=
  if toss_valid p then valid_toss p else mzero.

Lemma toss_mass p : toss p setT = if toss_valid p then 1 else 0.
Proof. by rewrite /toss; case: ifP => _ //; rewrite probability_setT. Qed.

Lemma toss_mass_le1 p : toss p setT <= 1.
Proof. by rewrite toss_mass; case: (toss_valid p); [exact: lexx | exact: lee01]. Qed.

Lemma toss_invalid p A : ~~ toss_valid p -> toss p A = 0.
Proof. by move=> /negbTE h; rewrite /toss h. Qed.

Lemma toss_point p b : toss_valid p -> toss p [set b] = (bernoulli_pmf p b)%:E.
Proof.
move=> h; rewrite /toss h.
change (bernoulli_prob p [set b] = (bernoulli_pmf p b)%:E).
move: h; rewrite /toss_valid => h.
by rewrite /bernoulli_prob h fsbig_set1.
Qed.

End CoinLaw.
