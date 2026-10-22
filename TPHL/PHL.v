(** TPHL: truth-functional probabilistic Hoare logic for pWHILE over a
    countable domain (paper: "A Complete Truth-functional Probabilistic Hoare
    Logic").  This file holds the shared definitions only, following the
    layout of CPHL.v:
      - the domain signature and valuations (Sec. 2.2),
      - the classical and probabilistic assertion syntax of PPL and its
        semantics (Figs. 1-2),
      - pWHILE and its kernel semantics (Fig. 4, App. A),
      - semantic validity of formulas and Hoare triples (Def. 5),
      - the syntactic transformations used by the rules (Figs. 8-9),
      - the proof system (Fig. 6) as the inductive [hoare_derivable].
    Proofs about these definitions live in Soundness/ and Completeness/. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

(** Analytical notation stays inside modules and sections, so the syntax and
    later example files keep a Stdlib-facing interface. *)
Require AnalysisPrelude.
Require MeasureIntegration.
Require CoinLaw.
From HB Require Import structures.
Import MeasureIntegration.
From mathcomp Require boot order ssralg ssrnum boolp classical_sets.
From mathcomp Require reals topology ereal measure Rstruct.
From mathcomp Require functions normedtype sequences esum lebesgue_integral.
From mathcomp Require kernel Rstruct_topology measurable_realfun lebesgue_measure.

Open Scope R_scope.
Open Scope string_scope.
Import ListNotations.

(* ================================================================== *)
(** * Domains *)
(* ================================================================== *)

(** The paper fixes a countable domain [D] with finitely many function and
    predicate symbols.  Here a domain packs its carrier with decidable
    equality, binary operation symbols and binary relation symbols.  Unary
    symbols are encoded by ignoring one argument; higher arities are not
    needed by the examples.  Countability/finiteness is not part of the
    signature: soundness holds for any carrier, and the completeness results
    assume finiteness explicitly. *)
Record Domain : Type := {
  dom_carrier :> Type;
  dom_eq_dec : forall x y : dom_carrier, {x = y} + {x <> y};
  dom_op : Type;
  dom_op_eval : dom_op -> dom_carrier -> dom_carrier -> dom_carrier;
  dom_rel : Type;
  dom_rel_eval : dom_rel -> dom_carrier -> dom_carrier -> bool
}.

(* ================================================================== *)
(** * Variables *)
(* ================================================================== *)

(** The four classes of classical variables of the paper (program/logic,
    domain-valued/Boolean), plus the real-valued probabilistic logic
    variables [Y].  They are nominally distinct even though each is named by a
    string. *)
Inductive DomProgramVar : Type := dom_program_var (name : string).
Inductive BoolProgramVar : Type := bool_program_var (name : string).
Inductive DomLogicVar : Type := dom_logic_var (name : string).
Inductive BoolLogicVar : Type := bool_logic_var (name : string).
Inductive ProbLogicVar : Type := prob_logic_var (name : string).

Definition dom_program_var_eq_dec : forall x y : DomProgramVar, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.
Definition bool_program_var_eq_dec : forall x y : BoolProgramVar, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.
Definition dom_logic_var_eq_dec : forall x y : DomLogicVar, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.
Definition bool_logic_var_eq_dec : forall x y : BoolLogicVar, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.
Definition prob_logic_var_eq_dec : forall x y : ProbLogicVar, {x = y} + {x <> y}.
Proof. decide equality; apply string_dec. Defined.

Section Syntax.
Context {D : Domain}.

(* ================================================================== *)
(** * Valuations and classical state formulas (Fig. 1, Sec. 2.2) *)
(* ================================================================== *)

(** A valuation assigns values to all four classes of classical variables.
    Programs update only the program fields; logic fields may still vary
    across the support of a probabilistic state. *)
Record valuation : Type := {
  dom_program_values : DomProgramVar -> D;
  bool_program_values : BoolProgramVar -> bool;
  dom_logic_values : DomLogicVar -> D;
  bool_logic_values : BoolLogicVar -> bool
}.

Definition state : Type := valuation.

(** Domain terms: [xm | x | c | op(t, t)]. *)
Inductive Term : Type :=
  | TProgVar (x : DomProgramVar)
  | TLogicVar (x : DomLogicVar)
  | TConst (c : D)
  | TOp (o : dom_op D) (t1 t2 : Term).

(** Classical state formulas: [bm | b | rel(t, t) | ff | gamma => gamma]. *)
Inductive CFormula : Type :=
  | FProgBool (b : BoolProgramVar)
  | FLogicBool (b : BoolLogicVar)
  | FRel (r : dom_rel D) (t1 t2 : Term)
  | FFalse
  | FImpl (gamma1 gamma2 : CFormula).

(** Derived classical connectives. *)
Definition c_true : CFormula := FImpl FFalse FFalse.
Definition c_not (gamma : CFormula) : CFormula := FImpl gamma FFalse.
Definition c_and (gamma1 gamma2 : CFormula) : CFormula :=
  c_not (FImpl gamma1 (c_not gamma2)).
Definition c_or (gamma1 gamma2 : CFormula) : CFormula :=
  FImpl (c_not gamma1) gamma2.
Definition c_iff (gamma1 gamma2 : CFormula) : CFormula :=
  c_and (FImpl gamma1 gamma2) (FImpl gamma2 gamma1).

Fixpoint term_eval (t : Term) (v : state) : D :=
  match t with
  | TProgVar x => dom_program_values v x
  | TLogicVar x => dom_logic_values v x
  | TConst c => c
  | TOp o t1 t2 => dom_op_eval D o (term_eval t1 v) (term_eval t2 v)
  end.

Fixpoint satisfies (v : state) (gamma : CFormula) {struct gamma} : Prop :=
  match gamma with
  | FProgBool b => bool_program_values v b = true
  | FLogicBool b => bool_logic_values v b = true
  | FRel r t1 t2 => dom_rel_eval D r (term_eval t1 v) (term_eval t2 v) = true
  | FFalse => False
  | FImpl gamma1 gamma2 => satisfies v gamma1 -> satisfies v gamma2
  end.

(** Classical formulas are decidable on a valuation; guards are evaluated by
    this Boolean function, with no appeal to excluded middle. *)
Fixpoint cformula_eval_bool (gamma : CFormula) (v : state) : bool :=
  match gamma with
  | FProgBool b => bool_program_values v b
  | FLogicBool b => bool_logic_values v b
  | FRel r t1 t2 => dom_rel_eval D r (term_eval t1 v) (term_eval t2 v)
  | FFalse => false
  | FImpl gamma1 gamma2 =>
      implb (cformula_eval_bool gamma1 v) (cformula_eval_bool gamma2 v)
  end.

Lemma cformula_eval_bool_spec gamma v :
  cformula_eval_bool gamma v = true <-> satisfies v gamma.
Proof.
  induction gamma as [b | b | r t1 t2 | | gamma1 IH1 gamma2 IH2];
    cbn [cformula_eval_bool satisfies]; try reflexivity.
  - split; [discriminate | contradiction].
  - rewrite implb_true_iff, IH1, IH2; reflexivity.
Qed.

Lemma cformula_eval_bool_false gamma v :
  cformula_eval_bool gamma v = false <-> ~ satisfies v gamma.
Proof.
  rewrite <- not_true_iff_false, cformula_eval_bool_spec; reflexivity.
Qed.

(** Semantic classical assertions are predicates on valuations. *)
Definition Assertion : Type := state -> Prop.

Definition formula_assertion (gamma : CFormula) : Assertion :=
  fun v => satisfies v gamma.

(** Point updates of program variables. *)
Definition update_dom (v : state) (x : DomProgramVar) (c : D) : state :=
  {| dom_program_values :=
       fun y => if dom_program_var_eq_dec y x then c else dom_program_values v y;
     bool_program_values := bool_program_values v;
     dom_logic_values := dom_logic_values v;
     bool_logic_values := bool_logic_values v |}.

Definition update_bool (v : state) (b : BoolProgramVar) (value : bool) : state :=
  {| dom_program_values := dom_program_values v;
     bool_program_values :=
       fun c => if bool_program_var_eq_dec c b then value else bool_program_values v c;
     dom_logic_values := dom_logic_values v;
     bool_logic_values := bool_logic_values v |}.

(* ================================================================== *)
(** * pWHILE syntax (Fig. 4) *)
(* ================================================================== *)

(** The toss rate is an arbitrary real; rates outside [0,1] denote the zero
    kernel (as in CPHL), which keeps the syntax free of proof terms. *)
Inductive Cmd : Type :=
  | CSkip
  | CDomAssign (x : DomProgramVar) (t : Term)
  | CBoolAssign (b : BoolProgramVar) (beta : CFormula)
  | CBoolToss (b : BoolProgramVar) (r : R)
  | CSeq (c1 c2 : Cmd)
  | CIf (beta : CFormula) (c1 c2 : Cmd)
  | CWhile (beta : CFormula) (body : Cmd).

End Syntax.

Arguments Term : clear implicits.
Arguments CFormula : clear implicits.
Arguments valuation : clear implicits.
Arguments state : clear implicits.
Arguments Assertion : clear implicits.
Arguments Cmd : clear implicits.

(* ================================================================== *)
(** * Measurable state space and measures *)
(* ================================================================== *)

(** States carry the discrete sigma-algebra: every set of valuations is
    measurable.  It is presented as the sigma-algebra generated by all sets,
    which gives MathComp's [measurableType] structure for free.  With this
    choice every formula event, every assignment and every guard is
    measurable, so no measurability side conditions appear in the logic. *)
Module ValuationSpace.
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology measure Rstruct.
Local Open Scope classical_set_scope.

Section Space.
Context {D : Domain}.

Definition RawValuation := {classic valuation D}.
Definition Valuation := g_sigma_algebraType (@setT (set RawValuation)).

Lemma all_measurable (A : set Valuation) : measurable A.
Proof. exact: sub_sigma_algebra. Qed.

Lemma measurable_from_valuation {d} {Y : measurableType d} (f : Valuation -> Y) :
  measurable_fun setT f.
Proof. move=> _ B _; exact: all_measurable. Qed.

(** Functions out of [Valuation * bool] are measurable too: every subset of
    the product is a union of two measurable rectangles. *)
Lemma all_measurable_bool_pair (S : set (Valuation * bool)) : measurable S.
Proof.
  have -> : S = ([set v | S (v, true)] `*` [set true]) `|`
                ([set v | S (v, false)] `*` [set false]).
    apply/seteqP; split.
    - by move=> [v []] h; [left | right].
    - by move=> [v b] [[/= h ->] | [/= h ->]].
  by apply: measurableU; apply: measurableX; try exact: all_measurable.
Qed.

Lemma measurable_from_bool_pair {d} {Y : measurableType d}
  (f : Valuation * bool -> Y) : measurable_fun setT f.
Proof. move=> _ B _; exact: all_measurable_bool_pair. Qed.

End Space.
End ValuationSpace.

Module StateMeasure.
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology measure Rstruct.
Import ValuationSpace.
Local Open Scope classical_set_scope.

Section Measures.
Context {D : Domain}.
Definition Space := [the measurableType _ of @Valuation D].
Definition carrier : Type := @ConcreteMeasure.measure _ Space.

Lemma additive (mu : carrier) (A B : Assertion D) : ConcreteMeasure.Finite mu ->
  (forall v, ~ (A v /\ B v)) ->
  ConcreteMeasure.event_mass mu (fun v => A v \/ B v) =
    (ConcreteMeasure.event_mass mu A + ConcreteMeasure.event_mass mu B)%R.
Proof.
move=> hm h; apply: ConcreteMeasure.event_additive => //; try exact: all_measurable.
apply functional_extensionality => v; apply propext.
split => [hv|hf]; [exact: (h v hv) | contradiction].
Qed.
End Measures.
End StateMeasure.

Section MeasureInterface.
Context {D : Domain}.

(** Countably additive measures on valuations.  Being a sub-probability
    measure is a predicate, not a field (as in CPHL). *)
Definition Measure : Type := @StateMeasure.carrier D.
Definition Subprob : Measure -> Prop := ConcreteMeasure.Subprob.
Definition FiniteMeasure : Measure -> Prop := ConcreteMeasure.Finite.

(** [mu(A)] as a real number. *)
Definition measure_of : Measure -> Assertion D -> R := ConcreteMeasure.event_mass.

Lemma measure_additive : forall (mu : Measure) (A B : Assertion D),
  FiniteMeasure mu -> (forall v, ~ (A v /\ B v)) ->
  measure_of mu (fun v => A v \/ B v) = (measure_of mu A + measure_of mu B)%R.
Proof. exact StateMeasure.additive. Qed.

Lemma measure_empty : forall mu : Measure, measure_of mu (fun _ => False) = 0%R.
Proof. intro mu; apply ConcreteMeasure.event_empty. Qed.

Lemma measure_extensional : forall (mu : Measure) (A B : Assertion D),
  (forall v, A v <-> B v) -> measure_of mu A = measure_of mu B.
Proof.
  intros mu A B h; assert (A = B) as ->.
  { apply functional_extensionality; intro v; apply boolp.propext; apply h. }
  reflexivity.
Qed.

Lemma measure_nonnegative : forall (mu : Measure) (A : Assertion D),
  (0 <= measure_of mu A)%R.
Proof.
  intros mu A; exact (ssrbool.elimT Rstruct.RleP
    (ConcreteMeasure.event_nonnegative mu A)).
Qed.

Lemma measure_subprobability : forall mu : Measure, Subprob mu ->
  (measure_of mu (fun _ => True) <= 1)%R.
Proof.
  intros mu hm; exact (ssrbool.elimT Rstruct.RleP (ConcreteMeasure.mass_bound hm)).
Qed.

End MeasureInterface.

Arguments Measure : clear implicits.

(* ================================================================== *)
(** * Probabilistic states and PPL (Figs. 1-2) *)
(* ================================================================== *)

Section Probabilistic.
Context {D : Domain}.

(** A probabilistic state pairs a measure with an assignment [rho] to the
    probabilistic logic variables; programs never change [rho]. *)
Record Pstate : Type := {
  pstate_measure : Measure D;
  pstate_prob_logic_values : ProbLogicVar -> R
}.

(** Def. 5 quantifies over sub-probability measures and arbitrary [rho]. *)
Definition pstate_admissible (ps : Pstate) : Prop := Subprob (pstate_measure ps).

(** Probability terms: [y | r | Pr(gamma) | p + p | p * p]. *)
Inductive Pterm : Type :=
  | PVar (y : ProbLogicVar)
  | PConst (r : R)
  | PProb (gamma : CFormula D)
  | PAdd (p1 p2 : Pterm)
  | PMul (p1 p2 : Pterm).

(** Probabilistic state formulas: [p <= p | fff | eta => eta]. *)
Inductive PFormula : Type :=
  | PFLe (p1 p2 : Pterm)
  | PFFalse
  | PFImpl (eta1 eta2 : PFormula).

Fixpoint pterm_eval (p : Pterm) (ps : Pstate) : R :=
  match p with
  | PVar y => pstate_prob_logic_values ps y
  | PConst r => r
  | PProb gamma => measure_of (pstate_measure ps) (formula_assertion gamma)
  | PAdd p1 p2 => pterm_eval p1 ps + pterm_eval p2 ps
  | PMul p1 p2 => pterm_eval p1 ps * pterm_eval p2 ps
  end.

Fixpoint psatisfies (ps : Pstate) (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 => pterm_eval p1 ps <= pterm_eval p2 ps
  | PFFalse => False
  | PFImpl eta1 eta2 => psatisfies ps eta1 -> psatisfies ps eta2
  end.

(** Derived connectives and abbreviations of Sec. 2.1. *)
Definition p_true : PFormula := PFImpl PFFalse PFFalse.
Definition p_not (eta : PFormula) : PFormula := PFImpl eta PFFalse.
Definition p_and (eta1 eta2 : PFormula) : PFormula :=
  p_not (PFImpl eta1 (p_not eta2)).
Definition p_or (eta1 eta2 : PFormula) : PFormula := PFImpl (p_not eta1) eta2.
Definition p_iff (eta1 eta2 : PFormula) : PFormula :=
  p_and (PFImpl eta1 eta2) (PFImpl eta2 eta1).
Definition p_eq (p1 p2 : Pterm) : PFormula := p_and (PFLe p1 p2) (PFLe p2 p1).
Definition p_lt (p1 p2 : Pterm) : PFormula := p_not (PFLe p2 p1).

(** [Box gamma] abbreviates [Pr(gamma) = Pr(tt)]. *)
Definition p_almost_sure (gamma : CFormula D) : PFormula :=
  p_eq (PProb gamma) (PProb c_true).

(** Validity of a probabilistic formula over admissible states (Sec. 2.2).
    This semantic notion plays the role of [TAUT]/PPL-provability in rule
    side conditions, as in CPHL. *)
Definition pformula_valid (eta : PFormula) : Prop :=
  forall ps : Pstate, pstate_admissible ps -> psatisfies ps eta.

(** Validity of a classical formula: true in every valuation. *)
Definition cformula_valid (gamma : CFormula D) : Prop :=
  forall v : state D, satisfies v gamma.

End Probabilistic.

Arguments Pstate : clear implicits.
Arguments Pterm : clear implicits.
Arguments PFormula : clear implicits.

(* ================================================================== *)
(** * Kernel semantics of pWHILE (Fig. 4, App. A) *)
(* ================================================================== *)

(** Commands denote sub-probability kernels from valuations to valuations.
    [run c] pushes an input measure through [denote c].  The construction
    follows CPHL's CommandSemantics: Dirac kernels for assignments, Kleisli
    composition for sequencing and tossing, a guard-selected branch for
    conditionals, and for loops the countable sum of the kernels that exit
    after exactly [n] body executions. *)
Module CommandSemantics.
Import boot order ssralg ssrnum boolp classical_sets.
Import reals topology ereal measure Rstruct.
Import functions normedtype sequences esum lebesgue_integral kernel Rstruct_topology.
Import measurable_realfun lebesgue_measure.
Import ValuationSpace.
Import Order.TTheory GRing.Theory Num.Theory.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section Kernels.
Context {D : Domain}.

Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).

Definition Kernel := real.-spker Valuation ~> Valuation.

(** Deterministic updates are Dirac kernels. *)
Definition skip : Valuation -> carrier :=
  kdirac (@measurable_id _ Valuation setT).
HB.instance Definition _ := ProbabilityKernel.on skip.

Definition dom_assign (x : DomProgramVar) (t : Term D) : Valuation -> carrier :=
  kdirac (measurable_from_valuation
            (fun v : Valuation => update_dom v x (term_eval t v) : Valuation)).
HB.instance Definition _ x t := ProbabilityKernel.on (dom_assign x t).

Definition bool_assign (b : BoolProgramVar) (beta : CFormula D) : Valuation -> carrier :=
  kdirac (measurable_from_valuation
            (fun v : Valuation => update_bool v b (cformula_eval_bool beta v) : Valuation)).
HB.instance Definition _ b beta := ProbabilityKernel.on (bool_assign b beta).

Definition bool_update (b : BoolProgramVar) : (Valuation * bool) -> carrier :=
  kdirac (measurable_from_bool_pair
            (fun p : Valuation * bool => update_bool p.1 b p.2 : Valuation)).
HB.instance Definition _ b := ProbabilityKernel.on (bool_update b).

(** The coin law does not depend on the incoming valuation. *)
Definition bool_law (r : R) (_ : Valuation) : {measure set bool -> \bar real} :=
  CoinLaw.CoinLaw.toss r.
Lemma bool_law_measurable r A : measurable A ->
  measurable_fun [set: Valuation] (bool_law r ^~ A).
Proof. move=> _; exact: measurable_from_valuation. Qed.
HB.instance Definition _ r := isKernel.Build _ _ _ _ _
  (bool_law r) (bool_law_measurable r).
Lemma bool_law_subprob r :
  ereal_sup [set bool_law r v setT | v in [set: Valuation]] <= 1.
Proof. apply: ge_ereal_sup => _ [v _ <-]; exact: CoinLaw.CoinLaw.toss_mass_le1. Qed.
HB.instance Definition _ r := Kernel_isSubProbability.Build _ _ _ _ _
  (bool_law r) (bool_law_subprob r).

(** Parameterized composition keeps the incoming valuation available. *)
Section Bind.
Context {d} {Y : measurableType d}.
Variables (l : real.-spker Valuation ~> Y) (k : real.-spker (Valuation * Y) ~> Valuation).
Definition bind := mkcomp l k.
HB.instance Definition _ := Kernel.on bind.
Lemma bind_mass v : bind v setT <= 1.
Proof.
apply: (@le_trans _ _ (\int[l v]__ 1)); last first.
  by rewrite integral_cst// mul1e; exact: sprob_kernel_le1.
apply: ge0_le_integral => //.
- exact: measurableT_comp (measurable_kernel k _ measurableT) _.
- by move=> y _; exact: sprob_kernel_le1.
Qed.
HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ bind
  ((sprob_kernelP bind).2 bind_mass).
End Bind.

(** [toss(b, r)]: draw a Boolean from the coin law and store it in [b]. *)
Definition toss (b : BoolProgramVar) (r : R) :=
  bind [the real.-spker _ ~> _ of bool_law r] [the real.-spker _ ~> _ of bool_update b].
HB.instance Definition _ b r := SubProbabilityKernel.on (toss b r).

(** Lift a kernel to ignore an extra parameter (used by sequencing). *)
Section After.
Context {d} {X : measurableType d}.
Variable k : Kernel.
Definition after (p : X * Valuation) : carrier := k p.2.
Lemma after_measurable A : measurable A -> measurable_fun setT (after ^~ A).
Proof. move=> mA; exact: measurableT_comp (measurable_kernel k _ mA) measurable_snd. Qed.
HB.instance Definition _ := isKernel.Build _ _ _ _ _ after after_measurable.
Lemma after_subprob : ereal_sup [set after p setT | p in setT] <= 1.
Proof. by apply: ge_ereal_sup => _ [p _ <-]; exact: sprob_kernel_le1. Qed.
HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ after after_subprob.
End After.

Definition sequence (k l : Kernel) := bind k [the real.-spker _ ~> _ of after l].
HB.instance Definition _ k l := SubProbabilityKernel.on (sequence k l).

(** Branch selection uses the pre-state guard and does not normalize. *)
Definition branch (gamma : CFormula D) (k l : Kernel) (v : Valuation) : carrier :=
  if cformula_eval_bool gamma v then k v else l v.
Lemma branch_measurable gamma k l A : measurable A ->
  measurable_fun setT (branch gamma k l ^~ A).
Proof. move=> _; exact: measurable_from_valuation. Qed.
HB.instance Definition _ gamma k l := isKernel.Build _ _ _ _ _
  (branch gamma k l) (branch_measurable gamma k l).
Lemma branch_subprob gamma k l :
  ereal_sup [set branch gamma k l v setT | v in setT] <= 1.
Proof.
apply: ge_ereal_sup => _ [v _ <-]; rewrite /branch.
by case: (cformula_eval_bool gamma v); exact: sprob_kernel_le1.
Qed.
HB.instance Definition _ gamma k l := Kernel_isSubProbability.Build _ _ _ _ _
  (branch gamma k l) (branch_subprob gamma k l).

(** A failed or still-running finite approximation contributes no output. *)
Definition zero : Valuation -> carrier := @kzero _ _ Valuation Valuation real.
HB.instance Definition _ := Kernel.on zero.
Lemma zero_subprob : ereal_sup [set zero v setT | v in setT] <= 1.
Proof. by apply: ge_ereal_sup => _ [v _ <-]; rewrite /zero /kzero /mzero lee_fin ler01. Qed.
HB.instance Definition _ := Kernel_isSubProbability.Build _ _ _ _ _ zero zero_subprob.

(** [loop_exit g k n] runs exactly [n] body iterations and then exits;
    [loop_approx g k n] exits after at most [n] iterations.  The paper's
    [sum_i (mu^i)|_{~beta}] is the series of the [loop_exit] kernels. *)
Fixpoint loop_exit g (k : Kernel) (n : nat) : Kernel :=
  match n with
  | O => [the real.-spker _ ~> _ of branch g
      [the real.-spker _ ~> _ of zero] [the real.-spker _ ~> _ of skip]]
  | S n => [the real.-spker _ ~> _ of branch g
      [the real.-spker _ ~> _ of sequence k (loop_exit g k n)]
      [the real.-spker _ ~> _ of zero]]
  end.
Fixpoint loop_approx g (k : Kernel) (n : nat) : Kernel :=
  match n with
  | O => loop_exit g k O
  | S n => [the real.-spker _ ~> _ of branch g
      [the real.-spker _ ~> _ of sequence k (loop_approx g k n)]
      [the real.-spker _ ~> _ of skip]]
  end.

Lemma sequence_event k l v A : sequence k l v A = \int[k v]_w l w A.
Proof. reflexivity. Qed.
Lemma loop_exit0 g k v A : loop_exit g k O v A =
  if cformula_eval_bool g v then 0 else dirac v A.
Proof.
change ((if cformula_eval_bool g v then zero v else skip v) A =
  if cformula_eval_bool g v then 0 else dirac v A).
by case: (cformula_eval_bool g v).
Qed.
Lemma loop_exitS g k n v A : loop_exit g k n.+1 v A =
  if cformula_eval_bool g v then \int[k v]_w loop_exit g k n w A else 0.
Proof.
change ((if cformula_eval_bool g v then sequence k (loop_exit g k n) v else zero v) A =
  if cformula_eval_bool g v then \int[k v]_w loop_exit g k n w A else 0).
by case: (cformula_eval_bool g v).
Qed.
Lemma loop_approxS g k n v A : loop_approx g k n.+1 v A =
  if cformula_eval_bool g v then \int[k v]_w loop_approx g k n w A else dirac v A.
Proof.
change ((if cformula_eval_bool g v then sequence k (loop_approx g k n) v else skip v) A =
  if cformula_eval_bool g v then \int[k v]_w loop_approx g k n w A else dirac v A).
by case: (cformula_eval_bool g v).
Qed.

(** The finite identity that bounds the countable sum (App. A.2). *)
Lemma loop_approx_sum g k n v A : measurable A ->
  loop_approx g k n v A = \sum_(i < n.+1) loop_exit g k i v A.
Proof.
move=> mA; elim: n v => [v|n ih v]; first by rewrite big_ord1.
rewrite loop_approxS big_ord_recl loop_exit0.
case hg: (cformula_eval_bool g v).
- rewrite add0e.
  under eq_integral do rewrite ih.
  rewrite ge0_integral_sum//; first by move=> i; exact: measurable_kernel.
  by apply: eq_bigr => i _; rewrite loop_exitS hg.
- rewrite (eq_bigr (fun _ => 0)); last by rewrite big1 ?adde0.
  by move=> i _; rewrite loop_exitS hg.
Qed.

Definition loop g (k : Kernel) :=
  kseries (fun n => (loop_exit g k n : real.-ker Valuation ~> Valuation)).
HB.instance Definition _ g k := Kernel.on (loop g k).
(** Prop. 12 for loops: the series is a sub-probability kernel. *)
Lemma loop_mass g k v : loop g k v setT <= 1.
Proof.
apply: ConcreteMeasure.series_subprob => n.
case: n => [|n].
- change ((\sum_(i < 0) loop_exit g k i v setT) <= 1).
  by rewrite big_ord0 lee_fin ler01.
- change ((\sum_(i < n.+1) loop_exit g k i v setT) <= 1).
  rewrite -loop_approx_sum//; exact: sprob_kernel_le1.
Qed.
HB.instance Definition _ g k := Kernel_isSubProbability.Build _ _ _ _ _
  (loop g k) ((sprob_kernelP (loop g k)).2 (loop_mass g k)).

(** Total denotation of every command, including nested loops. *)
Fixpoint denote (c : Cmd D) : Kernel :=
  match c with
  | CSkip => [the real.-spker _ ~> _ of skip]
  | CDomAssign x t => [the real.-spker _ ~> _ of dom_assign x t]
  | CBoolAssign b g => [the real.-spker _ ~> _ of bool_assign b g]
  | CBoolToss b r => [the real.-spker _ ~> _ of toss b r]
  | CSeq a b => [the real.-spker _ ~> _ of sequence (denote a) (denote b)]
  | CIf g a b => [the real.-spker _ ~> _ of branch g (denote a) (denote b)]
  | CWhile g body => [the real.-spker _ ~> _ of loop g (denote body)]
  end.

(** Push a measure through a kernel: [transform k mu A = int_v k v A dmu]. *)
Definition constant_kernel (mu : carrier) (_ : unit) := mu.
Lemma constant_kernel_measurable mu A : measurable A ->
  measurable_fun setT (constant_kernel mu ^~ A).
Proof. by move=> _; exact: measurable_cst. Qed.
HB.instance Definition _ mu := isKernel.Build _ _ _ _ _
  (constant_kernel mu) (constant_kernel_measurable mu).

Definition transform (k : Kernel) (mu : carrier) : carrier :=
  mkcomp (constant_kernel mu) (after k) tt.

(** [[c]] as a measure transformer, and its lift to probabilistic states:
    the assignment to probabilistic logic variables is left unchanged. *)
Definition transform_cmd (c : Cmd D) (mu : carrier) : carrier :=
  transform (denote c) mu.

Definition run (c : Cmd D) (ps : Pstate D) : Pstate D :=
  {| pstate_measure := transform_cmd c (pstate_measure ps);
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

End Kernels.
End CommandSemantics.

(* ================================================================== *)
(** * Validity of Hoare triples (Def. 5) *)
(* ================================================================== *)

Section Validity.
Context {D : Domain}.

(** [|= {pre} c {post}]: every admissible state satisfying [pre] is mapped by
    [c] to a state satisfying [post].  This is total-correctness style:
    divergence shows up as missing mass, and the zero measure must satisfy
    [post] as well. *)
Definition hoare_valid (pre : PFormula D) (c : Cmd D) (post : PFormula D) : Prop :=
  forall ps : Pstate D, pstate_admissible ps -> psatisfies ps pre ->
    psatisfies (CommandSemantics.run c ps) post.

End Validity.

(* ================================================================== *)
(** * Syntactic transformations used by the proof rules *)
(* ================================================================== *)

Section Transformations.
Context {D : Domain}.

Local Notation Term := (Term D).
Local Notation CFormula := (CFormula D).
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).

(** Analytical terms and formulas contain no measure term (Fig. 3). *)
Fixpoint pterm_analytical (p : Pterm) : Prop :=
  match p with
  | PVar _ | PConst _ => True
  | PProb _ => False
  | PAdd p1 p2 | PMul p1 p2 => pterm_analytical p1 /\ pterm_analytical p2
  end.

Fixpoint pformula_analytical (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 => pterm_analytical p1 /\ pterm_analytical p2
  | PFFalse => True
  | PFImpl eta1 eta2 => pformula_analytical eta1 /\ pformula_analytical eta2
  end.

(** [y in PVar(p)], [y in PVar(eta)]. *)
Fixpoint prob_logic_var_occurs_pterm (y : ProbLogicVar) (p : Pterm) : Prop :=
  match p with
  | PVar y' => y = y'
  | PConst _ | PProb _ => False
  | PAdd p1 p2 | PMul p1 p2 =>
      prob_logic_var_occurs_pterm y p1 \/ prob_logic_var_occurs_pterm y p2
  end.

Fixpoint prob_logic_var_occurs_pformula (y : ProbLogicVar) (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 =>
      prob_logic_var_occurs_pterm y p1 \/ prob_logic_var_occurs_pterm y p2
  | PFFalse => False
  | PFImpl eta1 eta2 =>
      prob_logic_var_occurs_pformula y eta1 \/ prob_logic_var_occurs_pformula y eta2
  end.

(** [eta^{xm}_t]: substitution of a domain program variable by a term.  PPL
    has no binders, so substitution is structural. *)
Fixpoint subst_dom_term (x : DomProgramVar) (replacement : Term) (t : Term) : Term :=
  match t with
  | TProgVar x' => if dom_program_var_eq_dec x' x then replacement else TProgVar x'
  | TLogicVar y => TLogicVar y
  | TConst c => TConst c
  | TOp o t1 t2 => TOp o (subst_dom_term x replacement t1) (subst_dom_term x replacement t2)
  end.

Fixpoint subst_dom_cformula (x : DomProgramVar) (replacement : Term) (gamma : CFormula)
  : CFormula :=
  match gamma with
  | FProgBool b => FProgBool b
  | FLogicBool b => FLogicBool b
  | FRel r t1 t2 => FRel r (subst_dom_term x replacement t1) (subst_dom_term x replacement t2)
  | FFalse => FFalse
  | FImpl gamma1 gamma2 =>
      FImpl (subst_dom_cformula x replacement gamma1) (subst_dom_cformula x replacement gamma2)
  end.

Fixpoint subst_dom_pterm (x : DomProgramVar) (replacement : Term) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PProb gamma => PProb (subst_dom_cformula x replacement gamma)
  | PAdd p1 p2 => PAdd (subst_dom_pterm x replacement p1) (subst_dom_pterm x replacement p2)
  | PMul p1 p2 => PMul (subst_dom_pterm x replacement p1) (subst_dom_pterm x replacement p2)
  end.

Fixpoint subst_dom_pformula (x : DomProgramVar) (replacement : Term) (eta : PFormula)
  : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (subst_dom_pterm x replacement p1) (subst_dom_pterm x replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_dom_pformula x replacement eta1) (subst_dom_pformula x replacement eta2)
  end.

(** [eta^{bm}_beta]: substitution of a Boolean program variable. *)
Fixpoint subst_bool_cformula (b : BoolProgramVar) (replacement : CFormula) (gamma : CFormula)
  : CFormula :=
  match gamma with
  | FProgBool b' => if bool_program_var_eq_dec b' b then replacement else FProgBool b'
  | FLogicBool b' => FLogicBool b'
  | FRel r t1 t2 => FRel r t1 t2
  | FFalse => FFalse
  | FImpl gamma1 gamma2 =>
      FImpl (subst_bool_cformula b replacement gamma1) (subst_bool_cformula b replacement gamma2)
  end.

Fixpoint subst_bool_pterm (b : BoolProgramVar) (replacement : CFormula) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PProb gamma => PProb (subst_bool_cformula b replacement gamma)
  | PAdd p1 p2 => PAdd (subst_bool_pterm b replacement p1) (subst_bool_pterm b replacement p2)
  | PMul p1 p2 => PMul (subst_bool_pterm b replacement p1) (subst_bool_pterm b replacement p2)
  end.

Fixpoint subst_bool_pformula (b : BoolProgramVar) (replacement : CFormula) (eta : PFormula)
  : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (subst_bool_pterm b replacement p1) (subst_bool_pterm b replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_bool_pformula b replacement eta1) (subst_bool_pformula b replacement eta2)
  end.

(** [eta^y_p]: substitution of a probabilistic logic variable (ELIMV). *)
Fixpoint subst_prob_pterm (y : ProbLogicVar) (replacement : Pterm) (p : Pterm) : Pterm :=
  match p with
  | PVar y' => if prob_logic_var_eq_dec y' y then replacement else PVar y'
  | PConst r => PConst r
  | PProb gamma => PProb gamma
  | PAdd p1 p2 => PAdd (subst_prob_pterm y replacement p1) (subst_prob_pterm y replacement p2)
  | PMul p1 p2 => PMul (subst_prob_pterm y replacement p1) (subst_prob_pterm y replacement p2)
  end.

Fixpoint subst_prob_pformula (y : ProbLogicVar) (replacement : Pterm) (eta : PFormula)
  : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (subst_prob_pterm y replacement p1) (subst_prob_pterm y replacement p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 =>
      PFImpl (subst_prob_pformula y replacement eta1) (subst_prob_pformula y replacement eta2)
  end.

(** Tossed terms and formulas (Fig. 9):
    [toss(bm, Pr(gamma), r) = (1 - r) Pr(gamma^bm_ff) + r Pr(gamma^bm_tt)]. *)
Fixpoint toss_pterm (b : BoolProgramVar) (r : R) (p : Pterm) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst c => PConst c
  | PProb gamma =>
      PAdd (PMul (PConst (1 - r)) (PProb (subst_bool_cformula b FFalse gamma)))
           (PMul (PConst r) (PProb (subst_bool_cformula b c_true gamma)))
  | PAdd p1 p2 => PAdd (toss_pterm b r p1) (toss_pterm b r p2)
  | PMul p1 p2 => PMul (toss_pterm b r p1) (toss_pterm b r p2)
  end.

Fixpoint toss_pformula (b : BoolProgramVar) (r : R) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (toss_pterm b r p1) (toss_pterm b r p2)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 => PFImpl (toss_pformula b r eta1) (toss_pformula b r eta2)
  end.

(** Conditional terms and formulas (Fig. 8): [Pr(gamma')/gamma = Pr(gamma /\ gamma')]. *)
Fixpoint condition_pterm (p : Pterm) (gamma : CFormula) : Pterm :=
  match p with
  | PVar y => PVar y
  | PConst r => PConst r
  | PProb gamma' => PProb (c_and gamma gamma')
  | PAdd p1 p2 => PAdd (condition_pterm p1 gamma) (condition_pterm p2 gamma)
  | PMul p1 p2 => PMul (condition_pterm p1 gamma) (condition_pterm p2 gamma)
  end.

Fixpoint condition_pformula (eta : PFormula) (gamma : CFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (condition_pterm p1 gamma) (condition_pterm p2 gamma)
  | PFFalse => PFFalse
  | PFImpl eta1 eta2 => PFImpl (condition_pformula eta1 gamma) (condition_pformula eta2 gamma)
  end.

(** [eta1 Y_beta eta2 = eta1/beta /\ eta2/~beta] (precondition of IF). *)
Definition if_precondition (eta1 eta2 : PFormula) (beta : CFormula) : PFormula :=
  p_and (condition_pformula eta1 beta) (condition_pformula eta2 (c_not beta)).

(** [eta1/gamma1 /\ eta2/gamma2 /\ Box(gamma1 \/ gamma2)] (precondition of SUM). *)
Definition sum_precondition (eta1 eta2 : PFormula) (gamma1 gamma2 : CFormula) : PFormula :=
  p_and (p_and (condition_pformula eta1 gamma1) (condition_pformula eta2 gamma2))
        (p_almost_sure (c_or gamma1 gamma2)).

(** [Box gamma /\ Pr(tt) = 1]: the premise of every while-body triple. *)
Definition p_concentrated_unit (gamma : CFormula) : PFormula :=
  p_and (p_almost_sure gamma) (p_eq (PProb c_true) (PConst 1)).

(** Finite families used by the while rules are total functions on [nat],
    observed only below [m] (as in CPHL). *)
Fixpoint finite_c_or (m : nat) (formulas : nat -> CFormula) : CFormula :=
  match m with
  | O => FFalse
  | S m' => c_or (finite_c_or m' formulas) (formulas m')
  end.

Fixpoint finite_p_and (m : nat) (formulas : nat -> PFormula) : PFormula :=
  match m with
  | O => p_true
  | S m' => p_and (finite_p_and m' formulas) (formulas m')
  end.

Fixpoint finite_r_sum (m : nat) (terms : nat -> R) : R :=
  match m with
  | O => 0
  | S m' => finite_r_sum m' terms + terms m'
  end.

(** Postconditions of the body triples of [W^UB] and [W^LB]:
    [/\_j Pr(gamma_j) <= r_ij  /\  Pr(~beta /\ gamma) <= r_i], and dually. *)
Definition while_body_post_upper (m : nat) (regions : nat -> CFormula)
  (transition_row : nat -> R) (beta gamma : CFormula) (exit : R) : PFormula :=
  p_and
    (finite_p_and m (fun j => PFLe (PProb (regions j)) (PConst (transition_row j))))
    (PFLe (PProb (c_and (c_not beta) gamma)) (PConst exit)).

Definition while_body_post_lower (m : nat) (regions : nat -> CFormula)
  (transition_row : nat -> R) (beta gamma : CFormula) (exit : R) : PFormula :=
  p_and
    (finite_p_and m (fun j => PFLe (PConst (transition_row j)) (PProb (regions j))))
    (PFLe (PConst exit) (PProb (c_and (c_not beta) gamma))).

(** Side conditions of the while rules.  The boxed classical premises of
    Fig. 6 are stated as classical validity. *)
Definition while_regions_cover (m : nat) (beta : CFormula) (regions : nat -> CFormula)
  : Prop :=
  cformula_valid (FImpl beta (finite_c_or m regions)).

Definition while_regions_in_guard (m : nat) (beta : CFormula) (regions : nat -> CFormula)
  : Prop :=
  forall i, (i < m)%nat -> cformula_valid (FImpl (regions i) beta).

(** Quantifying over [j < i] checks each unordered pair once. *)
Definition while_regions_disjoint (m : nat) (regions : nat -> CFormula) : Prop :=
  forall i j, (i < m)%nat -> (j < i)%nat ->
    cformula_valid (c_not (c_and (regions i) (regions j))).

(** [/\_i ((r_i > 0) \/ \/_{j < i} (r_ij > 0))]. *)
Definition while_progress (m : nat) (transitions : nat -> nat -> R) (exits : nat -> R)
  : Prop :=
  forall i, (i < m)%nat ->
    (0 < exits i) \/ exists j, (j < i)%nat /\ (0 < transitions i j).

(** [x_i >= sum_j r_ij x_j + r_i] and [0 <= x_i <= 1]. *)
Definition while_upper_solution (m : nat) (solution : nat -> R)
  (transitions : nat -> nat -> R) (exits : nat -> R) : Prop :=
  forall i, (i < m)%nat ->
    finite_r_sum m (fun j => transitions i j * solution j) + exits i <= solution i /\
    0 <= solution i <= 1.

(** [x_i <= sum_j r_ij x_j + r_i] and [0 <= x_i <= 1]. *)
Definition while_lower_solution (m : nat) (solution : nat -> R)
  (transitions : nat -> nat -> R) (exits : nat -> R) : Prop :=
  forall i, (i < m)%nat ->
    solution i <= finite_r_sum m (fun j => transitions i j * solution j) + exits i /\
    0 <= solution i <= 1.

Definition coin_probability_valid (r : R) : Prop := 0 <= r <= 1.

End Transformations.

(* ================================================================== *)
(** * The proof system (Fig. 6) *)
(* ================================================================== *)

Section ProofSystem.
Context {D : Domain}.

Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).

(** [|- {pre} c {post}].  Pre- and postconditions are syntactic PPL formulas;
    [TAUT] is represented by semantic validity in the side conditions of
    [HConseq], as in CPHL. *)
Inductive hoare_derivable : PFormula -> Cmd D -> PFormula -> Prop :=
  (** [Pr-FREE]: analytical formulas are invariant. *)
  | HFree : forall (eta : PFormula) (s : Cmd D),
      pformula_analytical eta ->
      hoare_derivable eta s eta
  (** [SKIP] *)
  | HSkip : forall eta : PFormula,
      hoare_derivable eta CSkip eta
  (** [ASGR] *)
  | HDomAssign : forall (eta : PFormula) (x : DomProgramVar) (t : Term D),
      hoare_derivable (subst_dom_pformula x t eta) (CDomAssign x t) eta
  (** [ASGB] *)
  | HBoolAssign : forall (eta : PFormula) (b : BoolProgramVar) (beta : CFormula D),
      hoare_derivable (subst_bool_pformula b beta eta) (CBoolAssign b beta) eta
  (** [TOSS]; the paper's syntax restricts [r] to [0,1]. *)
  | HBoolToss : forall (eta : PFormula) (b : BoolProgramVar) (r : R),
      coin_probability_valid r ->
      hoare_derivable (toss_pformula b r eta) (CBoolToss b r) eta
  (** Not in the paper: an out-of-range rate denotes the zero kernel. *)
  | HBoolTossInvalid : forall (b : BoolProgramVar) (r : R),
      ~ coin_probability_valid r ->
      hoare_derivable p_true (CBoolToss b r) (p_eq (PProb c_true) (PConst 0))
  (** [SEQ] *)
  | HSeq : forall (eta1 eta2 eta3 : PFormula) (s1 s2 : Cmd D),
      hoare_derivable eta1 s1 eta2 ->
      hoare_derivable eta2 s2 eta3 ->
      hoare_derivable eta1 (CSeq s1 s2) eta3
  (** [CONS] *)
  | HConseq : forall (eta0 eta1 eta2 eta3 : PFormula) (s : Cmd D),
      pformula_valid (PFImpl eta0 eta1) ->
      hoare_derivable eta1 s eta2 ->
      pformula_valid (PFImpl eta2 eta3) ->
      hoare_derivable eta0 s eta3
  (** [OR] *)
  | HOr : forall (eta0 eta1 eta2 : PFormula) (s : Cmd D),
      hoare_derivable eta0 s eta2 ->
      hoare_derivable eta1 s eta2 ->
      hoare_derivable (p_or eta0 eta1) s eta2
  (** [AND] *)
  | HAnd : forall (eta0 eta1 eta2 : PFormula) (s : Cmd D),
      hoare_derivable eta0 s eta1 ->
      hoare_derivable eta0 s eta2 ->
      hoare_derivable eta0 s (p_and eta1 eta2)
  (** [ELIMV] *)
  | HElimv : forall (eta1 eta2 : PFormula) (y : ProbLogicVar) (p : Pterm) (s : Cmd D),
      hoare_derivable (p_and eta1 (p_eq (PVar y) p)) s eta2 ->
      ~ prob_logic_var_occurs_pterm y p ->
      ~ prob_logic_var_occurs_pformula y eta2 ->
      hoare_derivable (subst_prob_pformula y p eta1) s eta2
  (** [IF<=]: [y <= Pr(gamma)] in each branch. *)
  | HIfLe : forall (eta1 eta2 : PFormula) (beta gamma : CFormula D)
      (y1 y2 : ProbLogicVar) (s1 s2 : Cmd D),
      hoare_derivable eta1 s1 (PFLe (PVar y1) (PProb gamma)) ->
      hoare_derivable eta2 s2 (PFLe (PVar y2) (PProb gamma)) ->
      hoare_derivable (if_precondition eta1 eta2 beta) (CIf beta s1 s2)
        (PFLe (PAdd (PVar y1) (PVar y2)) (PProb gamma))
  (** [IF>=]: [Pr(gamma) <= y] in each branch. *)
  | HIfGe : forall (eta1 eta2 : PFormula) (beta gamma : CFormula D)
      (y1 y2 : ProbLogicVar) (s1 s2 : Cmd D),
      hoare_derivable eta1 s1 (PFLe (PProb gamma) (PVar y1)) ->
      hoare_derivable eta2 s2 (PFLe (PProb gamma) (PVar y2)) ->
      hoare_derivable (if_precondition eta1 eta2 beta) (CIf beta s1 s2)
        (PFLe (PProb gamma) (PAdd (PVar y1) (PVar y2)))
  (** [W~]: a loop that is never entered. *)
  | HWhileNot : forall (beta gamma : CFormula D) (body : Cmd D) (y : ProbLogicVar),
      hoare_derivable
        (p_and (p_almost_sure (c_and (c_not beta) gamma)) (p_eq (PProb c_true) (PVar y)))
        (CWhile beta body)
        (p_and (p_eq (PProb gamma) (PProb c_true)) (p_eq (PProb c_true) (PVar y)))
  (** [W^UB_{m,k}] (regions indexed [0..m-1], [k < m]). *)
  | HWhileUpper : forall (m k : nat) (beta gamma : CFormula D) (body : Cmd D)
      (regions : nat -> CFormula D) (solution exits : nat -> R)
      (transitions : nat -> nat -> R) (y : ProbLogicVar),
      (k < m)%nat ->
      while_regions_cover m beta regions ->
      (forall i, (i < m)%nat ->
        hoare_derivable (p_concentrated_unit (regions i)) body
          (while_body_post_upper m regions (transitions i) beta gamma (exits i))) ->
      while_upper_solution m solution transitions exits ->
      hoare_derivable
        (p_and (p_almost_sure (c_and beta (regions k))) (PFLe (PProb c_true) (PVar y)))
        (CWhile beta body)
        (PFLe (PProb gamma) (PMul (PConst (solution k)) (PVar y)))
  (** [W^LB_{m,k}] (regions indexed [0..m-1], [k < m]). *)
  | HWhileLower : forall (m k : nat) (beta gamma : CFormula D) (body : Cmd D)
      (regions : nat -> CFormula D) (solution exits : nat -> R)
      (transitions : nat -> nat -> R) (y : ProbLogicVar),
      (k < m)%nat ->
      while_regions_in_guard m beta regions ->
      while_regions_disjoint m regions ->
      while_progress m transitions exits ->
      (forall i, (i < m)%nat ->
        hoare_derivable (p_concentrated_unit (regions i)) body
          (while_body_post_lower m regions (transitions i) beta gamma (exits i))) ->
      while_lower_solution m solution transitions exits ->
      hoare_derivable
        (p_and (p_almost_sure (c_and beta (regions k))) (PFLe (PVar y) (PProb c_true)))
        (CWhile beta body)
        (PFLe (PMul (PConst (solution k)) (PVar y)) (PProb gamma))
  (** [SUM<=] *)
  | HSumLe : forall (eta1 eta2 : PFormula) (gamma1 gamma2 gamma : CFormula D)
      (y1 y2 : ProbLogicVar) (s : Cmd D),
      cformula_valid (c_not (c_and gamma1 gamma2)) ->
      hoare_derivable (p_and eta1 (p_almost_sure gamma1)) s (PFLe (PVar y1) (PProb gamma)) ->
      hoare_derivable (p_and eta2 (p_almost_sure gamma2)) s (PFLe (PVar y2) (PProb gamma)) ->
      hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) s
        (PFLe (PAdd (PVar y1) (PVar y2)) (PProb gamma))
  (** [SUM>=] *)
  | HSumGe : forall (eta1 eta2 : PFormula) (gamma1 gamma2 gamma : CFormula D)
      (y1 y2 : ProbLogicVar) (s : Cmd D),
      cformula_valid (c_not (c_and gamma1 gamma2)) ->
      hoare_derivable (p_and eta1 (p_almost_sure gamma1)) s (PFLe (PProb gamma) (PVar y1)) ->
      hoare_derivable (p_and eta2 (p_almost_sure gamma2)) s (PFLe (PProb gamma) (PVar y2)) ->
      hoare_derivable (sum_precondition eta1 eta2 gamma1 gamma2) s
        (PFLe (PProb gamma) (PAdd (PVar y1) (PVar y2))).

End ProofSystem.

(* ================================================================== *)
(** * The natural-number domain used by the examples *)
(* ================================================================== *)

Inductive NatOp : Type := NAdd | NSub | NMul | NMod.
Inductive NatRel : Type := NLe | NEq | NLt.

Definition nat_op_eval (o : NatOp) (a b : nat) : nat :=
  match o with
  | NAdd => a + b
  | NSub => a - b
  | NMul => a * b
  | NMod => Nat.modulo a b
  end.

Definition nat_rel_eval (r : NatRel) (a b : nat) : bool :=
  match r with
  | NLe => Nat.leb a b
  | NEq => Nat.eqb a b
  | NLt => Nat.ltb a b
  end.

Definition nat_domain : Domain :=
  {| dom_carrier := nat;
     dom_eq_dec := Nat.eq_dec;
     dom_op := NatOp;
     dom_op_eval := nat_op_eval;
     dom_rel := NatRel;
     dom_rel_eval := nat_rel_eval |}.

(** Compilation checks. *)
Example nat_term_eval :
  term_eval (D := nat_domain) (TOp (D := nat_domain) NAdd (TConst (D := nat_domain) 2%nat) (TConst (D := nat_domain) 3%nat))
    (@Build_valuation nat_domain (fun _ => 0%nat) (fun _ => true)
       (fun _ => 0%nat) (fun _ => true)) = 5%nat.
Proof. reflexivity. Qed.

Example coin_program : Cmd nat_domain :=
  CSeq (CBoolToss (bool_program_var "b") (1/2))
       (CIf (FProgBool (bool_program_var "b"))
            (CDomAssign (dom_program_var "x") (TConst (D := nat_domain) 1%nat))
            (CDomAssign (dom_program_var "x") (TConst (D := nat_domain) 2%nat))).

Example rejection_sampling_loop : Cmd nat_domain :=
  CWhile (c_and (FProgBool (bool_program_var "b0")) (FProgBool (bool_program_var "b1")))
    (CSeq (CBoolToss (bool_program_var "b0") (1/2))
          (CBoolToss (bool_program_var "b1") (1/2))).
