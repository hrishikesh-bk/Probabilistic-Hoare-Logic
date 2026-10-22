(** Command equations: the kernel semantics of PHL.v agrees with the
    measure-transformer semantics of Fig. 4.  Adapted from CPHL's
    Soundness/CommandFacts.v.  Every set of valuations is measurable, so the
    equations hold on all events. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
From mathcomp Require Import bernoulli_distribution.
Require Import MeasureIntegration CoinLaw PHL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section CommandFacts.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Notation Kernel := (@Kernel D).
Local Notation skip := (@skip D).
Local Notation dom_assign := (@dom_assign D).
Local Notation bool_assign := (@bool_assign D).
Local Notation bool_update := (@bool_update D).
Local Notation bool_law := (@bool_law D).
Local Notation toss := (@toss D).
Local Notation sequence := (@sequence D).
Local Notation branch := (@branch D).
Local Notation transform := (@transform D).
Local Notation constant_kernel := (@constant_kernel D).
Local Notation after := (@after D _ _).
Local Notation bind := (@bind D _ _).

Lemma transform_event (k : Kernel) (mu : carrier) A :
  transform k mu A = \int[mu]_v k v A.
Proof. reflexivity. Qed.

(** Prop. 12: commands do not increase total mass. *)
Lemma transform_mass_nonincrease (k : Kernel) (mu : carrier) :
  transform k mu setT <= mu setT.
Proof.
rewrite transform_event -[leRHS]mul1e -integral_cst//.
apply: ge0_le_integral => //.
- exact: measurable_kernel.
- by move=> v _; exact: sprob_kernel_le1.
Qed.

Lemma transform_subprob (k : Kernel) (mu : carrier) :
  ConcreteMeasure.Subprob mu -> ConcreteMeasure.Subprob (transform k mu).
Proof. exact: le_trans (transform_mass_nonincrease k mu). Qed.

Lemma run_admissible c (ps : Pstate D) :
  pstate_admissible ps -> pstate_admissible (run c ps).
Proof. exact: transform_subprob. Qed.

Lemma run_external c (ps : Pstate D) :
  pstate_prob_logic_values (run c ps) = pstate_prob_logic_values ps.
Proof. reflexivity. Qed.

(** A finite source is an internal witness for the library's Fubini theorem;
    it does not change [transform]. *)
Definition finite_source (mu : carrier) (_ : ConcreteMeasure.Subprob mu) :=
  constant_kernel mu.
Arguments finite_source mu h : clear implicits.
HB.instance Definition _ mu h := Kernel.on (finite_source mu h).
Lemma finite_source_subprob mu h :
  ereal_sup [set finite_source mu h v setT | v in setT] <= 1.
Proof. by apply: ge_ereal_sup => _ [v _ <-]; exact: h. Qed.
HB.instance Definition _ mu h := Kernel_isSubProbability.Build _ _ _ _ _
  (finite_source mu h) (@finite_source_subprob mu h).

Lemma transform_integral (k : Kernel) (mu : carrier) f
    (hm : ConcreteMeasure.Subprob mu) :
  (forall v, 0 <= f v) -> measurable_fun [set: Valuation] f ->
  \int[transform k mu]_w f w = \int[mu]_v (\int[k v]_w f w).
Proof.
move=> f0 mf.
change (\int[mkcomp (finite_source mu hm) (after k) tt]_w f w =
  \int[mu]_v (\int[k v]_w f w)).
exact: integral_kcomp.
Qed.

Lemma bind_integral d (Y : measurableType d)
    (l : real.-spker Valuation ~> Y)
    (k : real.-spker (Valuation * Y) ~> Valuation) v f :
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[bind l k v]_w f w = \int[l v]_y (\int[k (v,y)]_w f w).
Proof. exact: integral_kcomp. Qed.

Lemma toss_integral b r v f :
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[toss b r v]_w f w = \int[bool_law r v]_z f (update_bool v b z).
Proof.
move=> f0 mf; rewrite /toss bind_integral//.
by apply: eq_integral => z _; rewrite /bool_update /kdirac integral_dirac// diracT mul1e.
Qed.

Lemma toss_mass b r v :
  toss b r v setT = if CoinLaw.toss_valid r then 1 else 0.
Proof.
rewrite /toss /bind /mkcomp /= /kcomp.
under eq_integral do rewrite /bool_update /kdirac /= diracT.
by rewrite integral_cst// mul1e CoinLaw.toss_mass.
Qed.

Lemma toss_invalid b r v A : ~~ CoinLaw.toss_valid r -> toss b r v A = 0.
Proof.
move=> /negbTE hr.
have hz : toss b r v setT = 0 by rewrite toss_mass hr.
exact: subset_measure0 (all_measurable _) measurableT (subsetT A) hz.
Qed.

(** For a rate in [0,1] the toss is the two-point law of Fig. 4. *)
Lemma toss_integral_valid b r v f : CoinLaw.toss_valid r ->
  (forall w, 0 <= f w) -> measurable_fun [set: Valuation] f ->
  \int[toss b r v]_w f w =
  r%:E * f (update_bool v b true) + (1 - r)%R%:E * f (update_bool v b false).
Proof.
move=> hr f0 mf; rewrite toss_integral// /bool_law /CoinLaw.toss hr.
exact: integral_bernoulli_prob.
Qed.

Lemma toss_event_valid b r v A : CoinLaw.toss_valid r ->
  toss b r v A =
  r%:E * (\1_A (update_bool v b true))%:E +
  (1 - r)%R%:E * (\1_A (update_bool v b false))%:E.
Proof.
move=> hr.
have mA : measurable A by exact: all_measurable.
transitivity (\int[toss b r v]_w (\1_A w)%:E).
  by rewrite integral_indic ?setIT.
rewrite toss_integral_valid//.
exact: measurable_from_valuation.
Qed.

(** Deterministic commands push the input measure forward. *)
Lemma transform_deterministic (f : Valuation -> Valuation)
    (mf : measurable_fun setT f) (mu : carrier) A :
  transform [the real.-spker _ ~> _ of kdirac mf] mu A = mu (f @^-1` A).
Proof.
rewrite transform_event.
rewrite (eq_integral (fun v => (\1_(f @^-1` A) v)%:E)).
  by move=> v _; rewrite /kdirac /= diracE indicE.
by rewrite integral_indic ?setIT//; exact: all_measurable.
Qed.

Lemma transform_skip (mu : carrier) A :
  transform [the real.-spker _ ~> _ of skip] mu A = mu A.
Proof. by rewrite transform_deterministic. Qed.

Lemma transform_dom_assign x t (mu : carrier) A :
  transform [the real.-spker _ ~> _ of dom_assign x t] mu A =
  mu ((fun v => update_dom v x (term_eval t v)) @^-1` A).
Proof. exact: transform_deterministic. Qed.

Lemma transform_bool_assign b g (mu : carrier) A :
  transform [the real.-spker _ ~> _ of bool_assign b g] mu A =
  mu ((fun v => update_bool v b (cformula_eval_bool g v)) @^-1` A).
Proof. exact: transform_deterministic. Qed.

Lemma transform_sequence (k l : Kernel) (mu : carrier) A :
  ConcreteMeasure.Subprob mu ->
  transform [the real.-spker _ ~> _ of sequence k l] mu A = transform l (transform k mu) A.
Proof.
move=> hm; rewrite !transform_event (transform_integral _ hm)//.
apply: measurable_kernel; exact: all_measurable.
Qed.

(** Branching restricts the input to the guard and its complement; the
    pieces are not normalized. *)
Lemma transform_branch g (k l : Kernel) (mu : carrier) A :
  transform [the real.-spker _ ~> _ of branch g k l] mu A =
  transform k (ConcreteMeasure.restrict mu (all_measurable (formula_assertion g))) A +
  transform l (ConcreteMeasure.restrict mu (all_measurable (~` formula_assertion g))) A.
Proof.
have mA : measurable A by exact: all_measurable.
rewrite !transform_event.
rewrite -!/(ConcreteMeasure.integral _ _) !ConcreteMeasure.integral_restrict//;
  try exact: measurable_kernel.
rewrite /ConcreteMeasure.integral.
rewrite -ge0_integralD//.
- by move=> v _; exact: erestrict_ge0.
- exact: measurable_from_valuation.
- by move=> v _; exact: erestrict_ge0.
- exact: measurable_from_valuation.
- apply: eq_integral => v _.
  change ((if cformula_eval_bool g v then k v else l v) A =
    ((fun w => k w A) \_ (formula_assertion g)) v +
    ((fun w => l w A) \_ (~` formula_assertion g)) v).
  rewrite !patchE.
  case: (boolP (v \in (formula_assertion g : set Valuation))) => hv.
  + have -> : cformula_eval_bool g v = true.
      by apply/cformula_eval_bool_spec; exact/set_mem.
    by rewrite in_setC hv /= adde0.
  + have -> : cformula_eval_bool g v = false.
      apply/negbTE; apply/negP => /cformula_eval_bool_spec h.
      by move: hv; rewrite (mem_set (h : (formula_assertion g : set Valuation) v)).
    by rewrite in_setC (negbTE hv) /= add0e.
Qed.

(** Linearity in the input measure (Props. 13 and 15). *)
Lemma transform_zero (k : Kernel) A : transform k mzero A = 0.
Proof. by rewrite transform_event integral_measure_zero. Qed.

Lemma transform_point (k : Kernel) v A : transform k (dirac v) A = k v A.
Proof.
have mf : measurable_fun [set: Valuation] (k ^~ A) := measurable_from_valuation _.
by rewrite transform_event integral_dirac// diracT mul1e.
Qed.

Lemma transform_add (k : Kernel) (mu nu : carrier) A :
  transform k (measure_add mu nu) A = transform k mu A + transform k nu A.
Proof.
rewrite !transform_event ge0_integral_measure_add//.
apply: measurable_kernel; exact: all_measurable.
Qed.

Lemma transform_scale (k : Kernel) (c : {nonneg real}) (mu : carrier) A :
  transform k (mscale c mu) A = c%:num%:E * transform k mu A.
Proof.
rewrite !transform_event ge0_integral_mscale//.
apply: measurable_kernel; exact: all_measurable.
Qed.

(** Transforms only see the input on events (extensionality). *)
Lemma transform_ext (k : Kernel) (mu nu : carrier) :
  (forall A, mu A = nu A) -> forall A, transform k mu A = transform k nu A.
Proof.
move=> h A; rewrite !transform_event.
by apply: eq_measure_integral => B mB _; exact: h.
Qed.

End CommandFacts.
