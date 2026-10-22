(** Correctness of the syntactic transformations used by the rules:
    substitution ([ASGR], [ASGB]), tossed formulas ([TOSS], Fig. 9), and
    conditioning ([IF], [SUM], Fig. 8).  Each transformed formula holds before
    a command (or of a restricted measure) iff the original formula holds
    after it. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CoinLaw PHL.
Require Import Soundness.StateFacts Soundness.CommandFacts Soundness.AssertionFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section MeasureLevel.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

(** Finite masses can be moved between [R] and [\bar R]. *)
Lemma measure_ofE (mu : carrier) (A : Assertion D) :
  ConcreteMeasure.Subprob mu -> (measure_of mu A)%:E = mu A.
Proof.
move=> h; apply: ConcreteMeasure.event_massE; last exact: all_measurable.
exact: ConcreteMeasure.subprob_finite.
Qed.

(** The measure of [gamma] after an assignment is the measure of the
    substituted formula before it. *)
Lemma transform_dom_assign_formula x t (mu : carrier) gamma :
  transform [the real.-spker _ ~> _ of @dom_assign D x t] mu (formula_assertion gamma) =
  mu (formula_assertion (subst_dom_cformula x t gamma)).
Proof.
rewrite transform_dom_assign; congr (mu _).
apply/seteqP; split => v /=; rewrite /preimage /formula_assertion /=;
  by rewrite subst_dom_cformula_correct.
Qed.

Lemma transform_bool_assign_formula b beta (mu : carrier) gamma :
  transform [the real.-spker _ ~> _ of @bool_assign D b beta] mu (formula_assertion gamma) =
  mu (formula_assertion (subst_bool_cformula b beta gamma)).
Proof.
rewrite transform_bool_assign; congr (mu _).
apply/seteqP; split => v /=; rewrite /preimage /formula_assertion /=;
  by rewrite subst_bool_cformula_correct.
Qed.

(** One branch of a toss: integrating a scaled indicator of an updated
    valuation gives the scaled mass of the preimage. *)
Lemma integral_toss_branch (mu : carrier) b (k : real) (B : set Valuation) (z : bool) :
  (0 <= k)%R ->
  \int[mu]_v (k%:E * (\1_B (update_bool v b z))%:E) =
  k%:E * mu ((fun v : Valuation => update_bool v b z : Valuation) @^-1` B).
Proof.
move=> k0.
have f0 : forall v, [set: Valuation] v -> 0 <= (\1_B (update_bool v b z) : real)%:E.
  by move=> v _; rewrite lee_fin.
have mf : measurable_fun [set: Valuation]
    (fun v : Valuation => (\1_B (update_bool v b z) : real)%:E).
  exact: (@measurable_from_valuation D _ _ _).
rewrite (ge0_integralZl_EFin mu measurableT f0 mf k0); congr (_ * _).
transitivity (\int[mu]_v (\1_((fun w : Valuation => update_bool w b z : Valuation) @^-1` B) v)%:E).
  by apply: eq_integral => v _; rewrite !indicE.
by rewrite integral_indic ?setIT//; exact: all_measurable.
Qed.

(** A valid toss is the convex combination of the two assignments. *)
Lemma transform_toss_formula b r (mu : carrier) gamma :
  CoinLaw.toss_valid r ->
  transform [the real.-spker _ ~> _ of @toss D b r] mu (formula_assertion gamma) =
  (1 - r)%R%:E * mu (formula_assertion (subst_bool_cformula b FFalse gamma)) +
  r%:E * mu (formula_assertion (subst_bool_cformula b c_true gamma)).
Proof.
move=> hr; have /andP [r0 r1] := hr.
have r0' : (0 <= 1 - r)%R by rewrite subr_ge0.
have pre z : formula_assertion (subst_bool_cformula b (if z then c_true else FFalse) gamma)
    = (fun v : Valuation => update_bool v b z : Valuation) @^-1`
        (formula_assertion gamma : set Valuation).
  apply/seteqP; split => v /=; rewrite /preimage /formula_assertion /=;
    by rewrite subst_bool_const_correct.
rewrite (pre false) (pre true) transform_event.
under eq_integral do rewrite toss_event_valid//.
rewrite (ge0_integralD _ measurableT); cbv beta;
  try (by move=> v _; apply: mule_ge0; rewrite lee_fin ?subr_ge0);
  try exact: (@measurable_from_valuation D _ _ _).
by rewrite !integral_toss_branch// addeC.
Qed.

Lemma transform_toss_invalid b r (mu : carrier) A :
  ~~ CoinLaw.toss_valid r ->
  transform [the real.-spker _ ~> _ of @toss D b r] mu A = 0.
Proof.
move=> hr; rewrite transform_event.
under eq_integral do rewrite toss_invalid//.
by rewrite integral0.
Qed.

(** Restriction to [gamma] turns [Pr(gamma')] into [Pr(gamma /\ gamma')]. *)
Lemma restrict_formula (mu : carrier) gamma gamma' :
  ConcreteMeasure.restrict mu (all_measurable (formula_assertion gamma))
    (formula_assertion gamma') =
  mu (formula_assertion (c_and gamma gamma')).
Proof.
rewrite /ConcreteMeasure.restrict /= /mrestr; congr (mu _).
apply: funext => v; apply: propext.
change (satisfies v gamma' /\ satisfies v gamma <-> satisfies v (c_and gamma gamma')).
rewrite satisfies_and; tauto.
Qed.

End MeasureLevel.

(** ** Formula level (Stdlib reals) *)

Section FormulaLevel.
Context {D : Domain}.
Local Open Scope R_scope.
Local Notation Pstate := (Pstate D).
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).
Implicit Types (ps : Pstate) (eta : PFormula) (p : Pterm) (gamma : CFormula D).

Lemma run_measure c ps :
  pstate_measure (run c ps) = transform_cmd c (pstate_measure ps).
Proof. reflexivity. Qed.

(** [ASGR] *)
Lemma subst_dom_pterm_run x t p ps :
  pterm_eval (subst_dom_pterm x t p) ps = pterm_eval p (run (CDomAssign x t) ps).
Proof.
  induction p as [y|r|gamma|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try congruence.
  unfold measure_of, ConcreteMeasure.event_mass. f_equal.
  symmetry. exact (transform_dom_assign_formula x t (pstate_measure ps) gamma).
Qed.

Lemma subst_dom_pformula_run x t eta ps :
  psatisfies ps (subst_dom_pformula x t eta) <-> psatisfies (run (CDomAssign x t) ps) eta.
Proof.
  induction eta; cbn; try tauto.
  by rewrite !subst_dom_pterm_run.
Qed.

(** [ASGB] *)
Lemma subst_bool_pterm_run b beta p ps :
  pterm_eval (subst_bool_pterm b beta p) ps = pterm_eval p (run (CBoolAssign b beta) ps).
Proof.
  induction p as [y|r|gamma|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try congruence.
  unfold measure_of, ConcreteMeasure.event_mass. f_equal.
  symmetry. exact (transform_bool_assign_formula b beta (pstate_measure ps) gamma).
Qed.

Lemma subst_bool_pformula_run b beta eta ps :
  psatisfies ps (subst_bool_pformula b beta eta) <->
  psatisfies (run (CBoolAssign b beta) ps) eta.
Proof.
  induction eta; cbn; try tauto.
  by rewrite !subst_bool_pterm_run.
Qed.

(** [TOSS] *)
Lemma toss_valid_iff r : CoinLaw.toss_valid r <-> coin_probability_valid r.
Proof.
  unfold CoinLaw.toss_valid, coin_probability_valid.
  split.
  - move=> /andP [h0 h1]; split; apply/Rstruct.RleP; assumption.
  - move=> [h0 h1]; apply/andP; split; apply/Rstruct.RleP; assumption.
Qed.

Lemma toss_pterm_run b r p ps :
  coin_probability_valid r -> pstate_admissible ps ->
  pterm_eval (toss_pterm b r p) ps = pterm_eval p (run (CBoolToss b r) ps).
Proof.
  intros hr hps.
  induction p as [y|c|gamma|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try congruence.
  apply EFin_inj.
  have hrun := run_admissible (CBoolToss b r) hps.
  rewrite EFinD !EFinM !measure_ofE //.
  exact (esym (transform_toss_formula b (pstate_measure ps) gamma
                 (proj2 (toss_valid_iff r) hr))).
Qed.

Lemma toss_pformula_run b r eta ps :
  coin_probability_valid r -> pstate_admissible ps ->
  psatisfies ps (toss_pformula b r eta) <-> psatisfies (run (CBoolToss b r) ps) eta.
Proof.
  intros hr hps. induction eta; cbn; try tauto.
  by rewrite !toss_pterm_run.
Qed.

Lemma run_toss_invalid_mass b r ps gamma :
  ~ coin_probability_valid r ->
  measure_of (pstate_measure (run (CBoolToss b r) ps)) (formula_assertion gamma) = 0.
Proof.
  intros hr. unfold measure_of, ConcreteMeasure.event_mass.
  rewrite run_measure.
  change (fine (transform [the real.-spker _ ~> _ of @toss D b r] (pstate_measure ps)
           (formula_assertion gamma)) = 0).
  have hn : ~~ CoinLaw.toss_valid r.
    by apply/negP => h; apply: hr; apply/toss_valid_iff.
  by rewrite transform_toss_invalid.
Qed.

(** [IF], [SUM]: conditioning is restriction. *)
Definition pstate_restrict ps gamma : Pstate :=
  {| pstate_measure := ConcreteMeasure.restrict (pstate_measure ps)
                         (all_measurable (formula_assertion gamma));
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

Lemma restrict_admissible ps gamma :
  pstate_admissible ps -> pstate_admissible (pstate_restrict ps gamma).
Proof. apply ConcreteMeasure.restrict_subprob. Qed.

Lemma condition_pterm_correct p gamma ps :
  pterm_eval (condition_pterm p gamma) ps = pterm_eval p (pstate_restrict ps gamma).
Proof.
  induction p as [y|r|gamma'|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try congruence.
  unfold measure_of, ConcreteMeasure.event_mass. f_equal.
  symmetry. apply restrict_formula.
Qed.

Lemma condition_pformula_correct eta gamma ps :
  psatisfies ps (condition_pformula eta gamma) <-> psatisfies (pstate_restrict ps gamma) eta.
Proof.
  induction eta; cbn; try tauto.
  by rewrite !condition_pterm_correct.
Qed.

End FormulaLevel.
