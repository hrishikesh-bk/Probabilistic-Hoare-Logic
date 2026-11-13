(** Semantics of [while beta do body] over the classes of a finite set of
    variables (App. D, proof of Lemma 25, while case).

    Fix a target formula [gamma] and let [V] collect the variables of the
    loop and of [gamma].  On each class [a] of [V]:
      - [xv a]: the probability that the loop exits in [gamma],
      - [rv a b]: the one-step probability of moving from [a] to class [b],
      - [ev a]: the one-step probability of exiting into [~beta /\ gamma],
    all well defined by the dependence lemma.  The output mass of [gamma] is
    [sum_a xv a * mu(gamma_a)], and on classes inside the guard
    [xv a = sum_b rv a b * xv b + ev a]. *)
From Stdlib Require Import Reals List Lra.
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
Require Import Completeness.FiniteDomain Completeness.Dependence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma lsum_e_EFin {X : Type} (l : list X) (f : X -> R) :
  lsum_e l (fun a => (f a)%:E) = (rsum l f)%:E.
Proof. by elim: l => [|x l IH] //=; rewrite IH EFinD. Qed.

Section LoopClasses.
Context {D : Domain} (FD : FiniteDomain D).
Variables (beta gamma : CFormula D) (body : Cmd D).

Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Notation classes := (classes FD).
Local Notation class_formula := (class_formula FD).
Local Notation class_value := (class_value FD).

Definition loop_cmd : Cmd D := CWhile beta body.

Definition loop_vars : list Var :=
  nodup var_eq_dec (cmd_vars loop_cmd ++ cformula_vars gamma).

Lemma loop_vars_incl_app l : List.incl l (cmd_vars loop_cmd ++ cformula_vars gamma) ->
  List.incl l loop_vars.
Proof. by move=> h v hv; apply/nodup_In; apply: h. Qed.

Lemma incl_beta : List.incl (cformula_vars beta) loop_vars.
Proof. by apply: loop_vars_incl_app => v hv; rewrite List.in_app_iff /=; left; rewrite List.in_app_iff; left. Qed.

Lemma incl_body : List.incl (cmd_vars body) loop_vars.
Proof. by apply: loop_vars_incl_app => v hv; rewrite List.in_app_iff /=; left; rewrite List.in_app_iff; right. Qed.

Lemma incl_loop : List.incl (cmd_vars loop_cmd) loop_vars.
Proof. by apply: loop_vars_incl_app => v hv; rewrite List.in_app_iff; left. Qed.

Lemma incl_gamma : List.incl (cformula_vars gamma) loop_vars.
Proof. by apply: loop_vars_incl_app => v hv; rewrite List.in_app_iff; right. Qed.

Local Notation V := loop_vars.
Definition cls := classes V.
Definition G (a : Assignment) : set Valuation := formula_assertion (class_formula a).
Local Notation K := (CommandSemantics.denote body).
Local Notation W := (CommandSemantics.denote loop_cmd).
Local Notation Gam := (formula_assertion gamma : set Valuation).
Local Notation Ex := (formula_assertion (c_and (c_not beta) gamma) : set Valuation).

Lemma vinv_Gam : vinv V Gam.
Proof. exact: vinv_formula incl_gamma. Qed.

Lemma vinv_Ex : vinv V Ex.
Proof.
apply: vinv_formula => v hv.
have : List.In v (cformula_vars beta) \/ List.In v (cformula_vars gamma).
  by move: hv; rewrite /= !List.in_app_iff /=; tauto.
by case=> h; [apply: incl_beta | apply: incl_gamma].
Qed.

Lemma vinv_G a : List.In a cls -> vinv V (G a).
Proof. exact: vinv_class. Qed.

Lemma kernel_fin (k : @Kernel D) w A : (fine (k w A))%:E = k w A.
Proof.
apply: fineK; rewrite ge0_fin_numE ?measure_ge0//.
exact: le_lt_trans (kernel_le1 _ _ _) (ltry 1).
Qed.

(** The class values. *)
Definition xv a : R := fine (class_value (fun z => W z Gam) a).
Definition rv a b : R := fine (class_value (fun z => K z (G b)) a).
Definition ev a : R := fine (class_value (fun z => K z Ex) a).
Definition en (n : nat) a : R := fine (class_value (fun z => loop_exit beta K n z Gam) a).

Lemma finv_kernel (k : @Kernel D) (A : set Valuation) :
  kinv V k -> vinv V A -> finv V (fun z => k z A).
Proof. by move=> hk hA w w' h; apply: hk. Qed.

Lemma kinv_W : kinv V W.
Proof. exact: kinv_denote incl_loop. Qed.

Lemma kinv_K : kinv V K.
Proof. exact: kinv_denote incl_body. Qed.

Lemma kinv_exit n : kinv V (loop_exit beta K n).
Proof. exact: kinv_loop_exit incl_beta kinv_K. Qed.

Lemma class_value_kernel (k : @Kernel D) A a w :
  kinv V k -> vinv V A -> List.In a cls -> satisfies w (class_formula a) ->
  (fine (class_value (fun z => k z A) a))%:E = k w A.
Proof.
move=> hk hA ha hw.
by rewrite (class_value_spec (finv_kernel hk hA) ha hw) kernel_fin.
Qed.

Lemma xvE a w : List.In a cls -> satisfies w (class_formula a) -> (xv a)%:E = W w Gam.
Proof. exact: class_value_kernel kinv_W vinv_Gam. Qed.

Lemma rvE a b w : List.In a cls -> List.In b cls -> satisfies w (class_formula a) ->
  (rv a b)%:E = K w (G b).
Proof. by move=> ha hb; exact: class_value_kernel kinv_K (vinv_G hb) ha. Qed.

Lemma evE a w : List.In a cls -> satisfies w (class_formula a) -> (ev a)%:E = K w Ex.
Proof. exact: class_value_kernel kinv_K vinv_Ex. Qed.

Lemma enE n a w : List.In a cls -> satisfies w (class_formula a) ->
  (en n a)%:E = loop_exit beta K n w Gam.
Proof. exact: class_value_kernel (kinv_exit n) vinv_Gam. Qed.

Lemma class_witness a : List.In a cls -> exists w, satisfies w (class_formula a).
Proof. by move=> ha; have [_ h] := proj1 (classes_spec FD V a) ha. Qed.

Lemma xv_bounds a : List.In a cls -> (0 <= xv a <= 1)%R.
Proof.
move=> ha; have [w hw] := class_witness ha.
have e := xvE ha hw; apply/andP; split.
- by rewrite -lee_fin e measure_ge0.
- by rewrite -lee_fin e; exact: kernel_le1.
Qed.

Lemma rv_ge0 a b : List.In a cls -> List.In b cls -> (0 <= rv a b)%R.
Proof.
move=> ha hb; have [w hw] := class_witness ha.
by rewrite -lee_fin (rvE ha hb hw) measure_ge0.
Qed.

Lemma ev_ge0 a : List.In a cls -> (0 <= ev a)%R.
Proof.
move=> ha; have [w hw] := class_witness ha.
by rewrite -lee_fin (evE ha hw) measure_ge0.
Qed.

(** Classes decide every formula over [V]. *)
Lemma class_decides g a : List.incl (cformula_vars g) V -> List.In a cls ->
  (forall w, satisfies w (class_formula a) -> satisfies w g) \/
  (forall w, satisfies w (class_formula a) -> ~ satisfies w g).
Proof.
move=> hg ha; have [w0 hw0] := class_witness ha.
case: (satisfies_dec w0 g) => h0; [left | right] => w hw.
- by apply/(satisfies_agree V g w0 w hg (classes_agree FD V a w0 w ha hw0 hw)).
- move=> hw'; apply: h0.
  by apply/(satisfies_agree V g w0 w hg (classes_agree FD V a w0 w ha hw0 hw)).
Qed.

Definition live (a : Assignment) : Prop :=
  forall w, satisfies w (class_formula a) -> satisfies w beta.

Definition liveb (a : Assignment) : bool := if pselect (live a) then true else false.

Definition live_cls : list Assignment := List.filter liveb cls.
Definition dead_cls : list Assignment := List.filter (fun a => ~~ liveb a) cls.

Lemma liveP a : liveb a = true <-> live a.
Proof. by rewrite /liveb; case: pselect. Qed.

Lemma dead_not_beta a w : List.In a cls -> liveb a = false ->
  satisfies w (class_formula a) -> ~ satisfies w beta.
Proof.
move=> ha hl hw hb; case: (class_decides incl_beta ha) => h.
- by have := proj2 (liveP a) h; rewrite hl.
- exact: h w hw hb.
Qed.

(** ** Output mass: the certificate is correct *)

Lemma lsum_classes_real (f : Assignment -> \bar real) (c : Assignment -> R) (mu : carrier) :
  ConcreteMeasure.Subprob mu ->
  (forall a, List.In a cls -> f a = (c a)%:E) ->
  lsum_e cls (fun a => f a * mu (G a)) =
  (rsum cls (fun a => (c a * measure_of mu (G a))%R))%:E.
Proof.
move=> hmu hf; rewrite -lsum_e_EFin; apply: lsum_e_ext => a ha.
by rewrite hf // EFinM measure_ofE.
Qed.

Lemma loop_output_mass (ps : Pstate D) : pstate_admissible ps ->
  measure_of (pstate_measure (run loop_cmd ps)) (formula_assertion gamma) =
  rsum cls (fun a => (xv a * measure_of (pstate_measure ps) (G a))%R).
Proof.
move=> hps; apply: EFin_inj.
have hr := run_admissible loop_cmd hps.
rewrite measure_ofE //.
rewrite /= /transform_cmd transform_event
  (@integral_classes D FD V (pstate_measure ps) _ (finv_kernel kinv_W vinv_Gam)
     (fun v => measure_ge0 _ _)).
apply: lsum_classes_real => // a ha.
by have [w hw] := class_witness ha; rewrite (class_value_spec (finv_kernel kinv_W vinv_Gam) ha hw) -(xvE ha hw).
Qed.

End LoopClasses.
