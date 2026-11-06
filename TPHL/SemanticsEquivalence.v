(** The paper's forward measure-transformer semantics and its equivalence
    with PHL.v's sub-probability kernels.  All measures are countably
    additive on the powerset of valuations; no countability or support
    assumption is made.  The syntax is the existing binary-signature Cmd.

    PaperSemantics is defined using measure operations only.  Invalid toss
    rates are extended to zero, as in PHL.v; valid_rates identifies the
    fragment on which the paper's equations apply without this extension.
    The correspondence does not formalize EPPL assertion provability. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CoinLaw PHL.
Require Import Soundness.CommandFacts Soundness.LoopFacts
  Soundness.AssertionFacts Soundness.HoareSoundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import ValuationSpace.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Module PaperSemantics.
Section Definitions.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (Measure D).

Definition restrict (mu : carrier) (g : CFormula D) : carrier :=
  ConcreteMeasure.restrict mu (all_measurable (formula_assertion g)).

Definition reject (mu : carrier) (g : CFormula D) : carrier :=
  ConcreteMeasure.restrict mu (all_measurable (~` formula_assertion g)).

Definition dom_assign x t (mu : carrier) : carrier :=
  ConcreteMeasure.push mu (measurable_from_valuation
    (fun v : Valuation => update_dom v x (term_eval t v) : Valuation)).

Definition bool_assign b g (mu : carrier) : carrier :=
  ConcreteMeasure.push mu (measurable_from_valuation
    (fun v : Valuation => update_bool v b (cformula_eval_bool g v) : Valuation)).

Lemma toss_complement_nonnegative (r : real) :
  CoinLaw.toss_valid r -> (0 <= 1 - r)%R.
Proof. move=> /andP [_ r1]; by rewrite subr_ge0. Qed.

Definition toss (b : BoolProgramVar) (r : real) (mu : carrier) : carrier.
Proof.
case: (boolP (CoinLaw.toss_valid r)) => hr.
- exact (ConcreteMeasure.add
    (ConcreteMeasure.scale (NngNum (andP hr).1) (bool_assign b c_true mu))
    (ConcreteMeasure.scale (NngNum (toss_complement_nonnegative hr))
      (bool_assign b FFalse mu))).
- exact ConcreteMeasure.zero.
Defined.

(** Forward recurrence: the nth measure is the input to the nth guard
    check, before restriction to either the continuing or exiting states. *)
Fixpoint iterates (g : CFormula D) (F : carrier -> carrier)
    (mu : carrier) (n : nat) : carrier :=
  match n with
  | O => mu
  | S n => F (restrict (iterates g F mu n) g)
  end.

Definition loop g F (mu : carrier) : carrier :=
  ConcreteMeasure.series (fun n => reject (iterates g F mu n) g).

Fixpoint transform_cmd (c : Cmd D) (mu : carrier) : carrier :=
  match c with
  | CSkip => mu
  | CDomAssign x t => dom_assign x t mu
  | CBoolAssign b g => bool_assign b g mu
  | CBoolToss b r => toss b r mu
  | CSeq a b => transform_cmd b (transform_cmd a mu)
  | CIf g a b => ConcreteMeasure.add
      (transform_cmd a (restrict mu g)) (transform_cmd b (reject mu g))
  | CWhile g body => loop g (transform_cmd body) mu
  end.

Definition run (c : Cmd D) (ps : Pstate D) : Pstate D :=
  {| pstate_measure := transform_cmd c (pstate_measure ps);
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

Fixpoint valid_rates (c : Cmd D) : Prop :=
  match c with
  | CBoolToss _ r => coin_probability_valid r
  | CSeq a b | CIf _ a b => valid_rates a /\ valid_rates b
  | CWhile _ body => valid_rates body
  | _ => True
  end.

Definition hoare_valid (pre : PFormula D) (c : Cmd D) (post : PFormula D) : Prop :=
  forall ps, pstate_admissible ps -> psatisfies ps pre ->
    psatisfies (run c ps) post.

Lemma restrict_event mu g A : restrict mu g A = mu (A `&` formula_assertion g).
Proof. reflexivity. Qed.

Lemma reject_event mu g A : reject mu g A = mu (A `&` ~` formula_assertion g).
Proof. reflexivity. Qed.

Lemma restrict_subprob mu g : Subprob mu -> Subprob (restrict mu g).
Proof. exact: ConcreteMeasure.restrict_subprob. Qed.

Lemma reject_subprob mu g : Subprob mu -> Subprob (reject mu g).
Proof. exact: ConcreteMeasure.restrict_subprob. Qed.

Lemma dom_assign_event x t mu A : dom_assign x t mu A =
  mu ((fun v => update_dom v x (term_eval t v)) @^-1` A).
Proof. reflexivity. Qed.

Lemma bool_assign_event b g mu A : bool_assign b g mu A =
  mu ((fun v => update_bool v b (cformula_eval_bool g v)) @^-1` A).
Proof. reflexivity. Qed.

Lemma toss_event_valid b r mu A : CoinLaw.toss_valid r ->
  toss b r mu A = r%:E * bool_assign b c_true mu A +
    (1 - r)%R%:E * bool_assign b FFalse mu A.
Proof.
move=> hr; rewrite /toss; destruct (boolP (CoinLaw.toss_valid r)) as [h | h]; last by rewrite hr in h.
by rewrite /ConcreteMeasure.add /= /measure_add /msum
  2!big_ord_recl /= big_ord0 adde0.
Qed.

Lemma toss_event_invalid b r mu A : ~~ CoinLaw.toss_valid r -> toss b r mu A = 0.
Proof.
move=> hr; rewrite /toss; destruct (boolP (CoinLaw.toss_valid r)) as [h | h].
- by rewrite h in hr.
- reflexivity.
Qed.

Lemma iterates_shift g F mu n :
  iterates g F mu n.+1 = iterates g F (F (restrict mu g)) n.
Proof.
elim: n => [|n ih]; first reflexivity.
change (F (restrict (iterates g F mu n.+1) g) =
  F (restrict (iterates g F (F (restrict mu g)) n) g)).
by rewrite ih.
Qed.

Lemma loop_event g F mu A :
  loop g F mu A = \sum_(n <oo) reject (iterates g F mu n) g A.
Proof. reflexivity. Qed.

End Definitions.
End PaperSemantics.

Section Equivalence.
Import CommandSemantics.
Context {D : Domain}.
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (Measure D).
Local Notation Kernel := (@CommandSemantics.Kernel D).

Lemma paper_measure_ext (mu nu : carrier) :
  (forall A, mu A = nu A) -> mu = nu.
Proof. move=> h; apply: eq_measure; exact/funext. Qed.

Lemma transform_paper_toss b r (mu : carrier) A :
  CommandSemantics.transform
    [the real.-spker _ ~> _ of @CommandSemantics.toss D b r] mu A =
  PaperSemantics.toss b r mu A.
Proof.
case: (boolP (CoinLaw.toss_valid r)) => hr.
- rewrite PaperSemantics.toss_event_valid// !PaperSemantics.bool_assign_event.
  rewrite transform_event.
  under eq_integral do rewrite toss_event_valid//.
  have r0 : (0 <= r)%R := (andP hr).1.
  have r1 : (0 <= 1 - r)%R by rewrite subr_ge0; exact: (andP hr).2.
  rewrite (eq_integral (fun v =>
    r%:E * (\1_((fun w : Valuation => update_bool w b true) @^-1` A) v)%:E +
    (1 - r)%R%:E * (\1_((fun w : Valuation => update_bool w b false) @^-1` A) v)%:E));
    first by move=> v _; rewrite !indicE.
  rewrite (ge0_integralD _ measurableT); cbv beta;
    try (by move=> v _; apply: mule_ge0; rewrite ?lee_fin);
    try exact: (@measurable_from_valuation D _ _ _).
  by rewrite !integral_scaled_indic//.
- rewrite PaperSemantics.toss_event_invalid// transform_event.
  under eq_integral do rewrite toss_invalid//.
  exact: integral0.
Qed.

Section LoopBridge.
Variables (g : CFormula D) (F : carrier -> carrier) (k : Kernel).
Hypothesis body_equiv : forall mu, Subprob mu ->
  forall A, F mu A = CommandSemantics.transform k mu A.

Lemma paper_body_subprob mu : Subprob mu -> Subprob (F mu).
Proof.
move=> hm; change (F mu setT <= 1).
rewrite body_equiv//; exact: transform_subprob.
Qed.

Lemma paper_iterates_subprob mu n : Subprob mu ->
  Subprob (PaperSemantics.iterates g F mu n).
Proof.
move=> hm; elim: n => // n ih /=.
apply: paper_body_subprob; exact: PaperSemantics.restrict_subprob.
Qed.

(** The finite bridge uses the forward recurrence, rather than defining
    the paper's loop in terms of kernel approximations. *)
Lemma transform_loop_exit_paper n mu : Subprob mu -> forall A,
  CommandSemantics.transform (CommandSemantics.loop_exit g k n) mu A =
  PaperSemantics.reject (PaperSemantics.iterates g F mu n) g A.
Proof.
elim: n mu => [mu hm A|n ih mu hm A].
- rewrite /CommandSemantics.loop_exit transform_branch.
  rewrite transform_skip transform_event.
  under eq_integral do rewrite /CommandSemantics.zero /kzero /mzero.
  by rewrite integral0 add0e.
- change (CommandSemantics.transform
    [the real.-spker _ ~> _ of CommandSemantics.branch g
      [the real.-spker _ ~> _ of CommandSemantics.sequence k
        (CommandSemantics.loop_exit g k n)]
      [the real.-spker _ ~> _ of @CommandSemantics.zero D]] mu A =
    PaperSemantics.reject (PaperSemantics.iterates g F mu n.+1) g A).
  rewrite transform_branch.
  have hrest : Subprob (PaperSemantics.restrict mu g) :=
    PaperSemantics.restrict_subprob g hm.
  rewrite transform_sequence//.
  have hbody : F (PaperSemantics.restrict mu g) =
      CommandSemantics.transform k (PaperSemantics.restrict mu g).
    apply: paper_measure_ext => B; exact: body_equiv.
  rewrite -hbody (ih _ (paper_body_subprob hrest)).
  rewrite transform_event.
  under eq_integral do rewrite /CommandSemantics.zero /kzero /mzero.
  by rewrite integral0 adde0 PaperSemantics.iterates_shift.
Qed.

Lemma transform_loop_paper mu : Subprob mu -> forall A,
  CommandSemantics.transform
    [the real.-spker _ ~> _ of CommandSemantics.loop g k] mu A =
  PaperSemantics.loop g F mu A.
Proof.
move=> hm A; rewrite transform_event PaperSemantics.loop_event.
under eq_integral do rewrite loop_event.
rewrite (@integral_nneseries _ Valuation real mu setT measurableT
  (fun n v => CommandSemantics.loop_exit g k n v A)
  (fun n => measurable_from_valuation _)
  (fun n v _ => measure_ge0 (CommandSemantics.loop_exit g k n v) A)).
apply: eq_eseriesr => n _.
exact: transform_loop_exit_paper.
Qed.

End LoopBridge.

(** Equality on every event, for arbitrary sub-probability inputs. *)
Theorem paper_semantics_equiv (c : Cmd D) (mu : carrier) : Subprob mu ->
  forall A, PaperSemantics.transform_cmd c mu A =
    CommandSemantics.transform_cmd c mu A.
Proof.
elim: c mu => [|x t|b g|b r|a iha b ihb|g a iha b ihb|g body ih] mu hm A.
- exact/esym/transform_skip.
- exact/esym/transform_dom_assign.
- exact/esym/transform_bool_assign.
- exact/esym/transform_paper_toss.
- change (PaperSemantics.transform_cmd b (PaperSemantics.transform_cmd a mu) A =
    CommandSemantics.transform
      [the real.-spker _ ~> _ of CommandSemantics.sequence
        (CommandSemantics.denote a) (CommandSemantics.denote b)] mu A).
  rewrite transform_sequence//.
  have ha : PaperSemantics.transform_cmd a mu = CommandSemantics.transform_cmd a mu.
    apply: paper_measure_ext => B; exact: iha.
  rewrite ha; apply: ihb; exact: transform_subprob.
- change (measure_add
    (PaperSemantics.transform_cmd a (PaperSemantics.restrict mu g))
    (PaperSemantics.transform_cmd b (PaperSemantics.reject mu g)) A =
    CommandSemantics.transform
      [the real.-spker _ ~> _ of CommandSemantics.branch g
        (CommandSemantics.denote a) (CommandSemantics.denote b)] mu A).
  rewrite measure_addE transform_branch.
  congr (_ + _).
  + apply: iha; exact: PaperSemantics.restrict_subprob.
  + apply: ihb; exact: PaperSemantics.reject_subprob.
- symmetry; apply: transform_loop_paper => // nu hnu B; exact: ih.
Qed.

Corollary paper_semantics_measure_eq (c : Cmd D) (mu : carrier) : Subprob mu ->
  PaperSemantics.transform_cmd c mu = CommandSemantics.transform_cmd c mu.
Proof. move=> hm; apply: paper_measure_ext => A; exact: paper_semantics_equiv. Qed.

Corollary paper_semantics_integral (c : Cmd D) (mu : carrier) : Subprob mu ->
  forall A, PaperSemantics.transform_cmd c mu A =
    \int[mu]_v CommandSemantics.denote c v A.
Proof. move=> hm A; rewrite paper_semantics_equiv//; exact: transform_event. Qed.

Corollary paper_semantics_mass_nonincrease (c : Cmd D) (mu : carrier) :
  Subprob mu -> PaperSemantics.transform_cmd c mu setT <= mu setT.
Proof.
move=> hm; rewrite paper_semantics_equiv//; exact: transform_mass_nonincrease.
Qed.

Corollary paper_semantics_subprob (c : Cmd D) (mu : carrier) :
  Subprob mu -> Subprob (PaperSemantics.transform_cmd c mu).
Proof. move=> hm; rewrite paper_semantics_measure_eq//; exact: transform_subprob. Qed.

(** On this fragment no invalid-rate extension is used.  The theorem is
    stronger than the paper's constant restrictions: all real valid rates
    are allowed, so its permitted constants are included. *)
Corollary paper_semantics_equiv_valid_rates (c : Cmd D) (mu : carrier) :
  PaperSemantics.valid_rates c -> Subprob mu ->
  PaperSemantics.transform_cmd c mu = CommandSemantics.transform_cmd c mu.
Proof. move=> _; exact: paper_semantics_measure_eq. Qed.

Lemma paper_run_same_masses (c : Cmd D) (ps : Pstate D) :
  pstate_admissible ps ->
  same_masses (PaperSemantics.run c ps) (CommandSemantics.run c ps).
Proof.
move=> hm; split => // gamma.
change (measure_of (PaperSemantics.transform_cmd c (pstate_measure ps))
    (formula_assertion gamma) =
  measure_of (CommandSemantics.transform_cmd c (pstate_measure ps))
    (formula_assertion gamma)).
by rewrite paper_semantics_measure_eq.
Qed.

Corollary paper_pterm_eval_equiv (c : Cmd D) (ps : Pstate D) (p : Pterm D) :
  pstate_admissible ps ->
  pterm_eval p (PaperSemantics.run c ps) = pterm_eval p (CommandSemantics.run c ps).
Proof. move=> hm; apply: pterm_eval_same_masses; exact: paper_run_same_masses. Qed.

Corollary paper_psatisfies_equiv (c : Cmd D) (ps : Pstate D) (eta : PFormula D) :
  pstate_admissible ps ->
  (psatisfies (PaperSemantics.run c ps) eta <->
   psatisfies (CommandSemantics.run c ps) eta).
Proof. move=> hm; apply: psatisfies_same_masses; exact: paper_run_same_masses. Qed.

Corollary paper_run_admissible (c : Cmd D) (ps : Pstate D) :
  pstate_admissible ps -> pstate_admissible (PaperSemantics.run c ps).
Proof. exact: paper_semantics_subprob. Qed.

Theorem paper_hoare_valid_iff (pre : PFormula D) (c : Cmd D) (post : PFormula D) :
  PaperSemantics.hoare_valid pre c post <-> hoare_valid pre c post.
Proof.
split=> h ps hm hp.
- apply/(paper_psatisfies_equiv c post hm); exact: h.
- apply/(paper_psatisfies_equiv c post hm); exact: h.
Qed.

(** Soundness transfers the existing Rocq calculus, whose assertion side
    conditions use semantic validity.  No EPPL completeness is assumed. *)
Corollary paper_hoare_derivable_sound (pre : PFormula D) (c : Cmd D)
    (post : PFormula D) :
  hoare_derivable pre c post -> PaperSemantics.hoare_valid pre c post.
Proof.
move=> h; apply/paper_hoare_valid_iff; exact: hoare_derivable_sound.
Qed.

Corollary paper_hoare_derivable_sound_valid_rates (pre : PFormula D)
    (c : Cmd D) (post : PFormula D) :
  PaperSemantics.valid_rates c -> hoare_derivable pre c post ->
  PaperSemantics.hoare_valid pre c post.
Proof. move=> _; exact: paper_hoare_derivable_sound. Qed.

End Equivalence.
