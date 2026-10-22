(** Equations satisfied by the class values of a loop (App. D, (b) and (c)
    in the proof of Lemma 25), and the layers [en n a] of exit probabilities
    after exactly [n] iterations, used to order classes for the progress
    condition of [W^LB]. *)
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
Require Import Completeness.FiniteDomain Completeness.Dependence Completeness.LoopClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section LoopEquations.
Context {D : Domain} (FD : FiniteDomain D).
Variables (beta gamma : CFormula D) (body : Cmd D).

Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Notation class_formula := (class_formula FD).
Local Notation class_value := (class_value FD).
Local Notation V := (loop_vars beta gamma body).
Local Notation cls := (cls FD beta gamma body).
Local Notation G := (G FD).
Local Notation K := (CommandSemantics.denote body).
Local Notation W := (CommandSemantics.denote (loop_cmd beta body)).
Local Notation Gam := (formula_assertion gamma : set Valuation).
Local Notation Ex := (formula_assertion (c_and (c_not beta) gamma) : set Valuation).
Local Notation xv := (xv FD beta gamma body).
Local Notation rv := (rv FD body).
Local Notation ev := (ev FD beta gamma body).
Local Notation en := (en FD beta gamma body).
Local Notation live_cls := (live_cls FD beta gamma body).
Local Notation dead_cls := (dead_cls FD beta gamma body).
Local Notation liveb := (liveb FD beta).
Local Notation kinvK := (@kinv_K D FD beta gamma body).
Local Notation kinvW := (@kinv_W D FD beta gamma body).
Local Notation vGam := (@vinv_Gam D beta gamma body).
Local Notation vEx := (@vinv_Ex D beta gamma body).

Lemma class_valueE (f : Valuation -> \bar real) a w :
  finv V f -> List.In a cls -> satisfies w (class_formula a) -> class_value f a = f w.
Proof. exact: class_value_spec. Qed.

(** ** A body run from a single class *)

(** If the input is concentrated on class [a], every event determined by
    [V] gets the class value times the input mass. *)
Lemma body_concentrated a (ps : Pstate D) (B : set Valuation) :
  List.In a cls -> vinv V B -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (class_formula a)) ->
  measure_of (pstate_measure (run body ps)) B =
  (fine (class_value (fun z => K z B) a) * measure_of (pstate_measure ps) (G a))%R.
Proof.
move=> ha hB hps /psatisfies_almost_sure hG.
set mu := pstate_measure ps.
have [w hw] := class_witness ha.
have hf := @finv_kernel D beta gamma body _ _ kinvK hB.
have hr := run_admissible body hps.
have hnull : mu (~` G a) = 0.
  rewrite -(measure_ofE _ hps).
  have -> : (~` G a) = (fun v => ~ satisfies v (class_formula a)) by [].
  by rewrite (measure_of_complement_null hps hG).
apply: EFin_inj; rewrite measure_ofE // EFinM measure_ofE //.
rewrite /= /transform_cmd transform_event
  (@integral_classes D FD V mu _ hf (fun v => measure_ge0 _ _)).
have hz : forall b, List.In b cls -> b <> a ->
    class_value (fun z => K z B) b * mu (formula_assertion (class_formula b)) = 0.
  move=> b hb hne.
  have -> : mu (formula_assertion (class_formula b)) = 0.
    apply/eqP; rewrite eq_le measure_ge0 andbT -hnull.
    apply: le_measure; rewrite ?inE; try exact: all_measurable.
    move=> v hv hva; apply: hne.
    exact: (classes_disjoint FD V b a v hb ha hv hva).
  by rewrite mule0.
rewrite (lsum_e_single (classes_nodup FD V) ha hz).
by rewrite (class_valueE hf ha hw) (@kernel_fin D K w B).
Qed.

(** ** Integrals against one body step from a class *)

Lemma integral_step a w (f : Valuation -> \bar real) (c : Assignment -> R) :
  List.In a cls -> satisfies w (class_formula a) -> finv V f -> (forall v, 0 <= f v) ->
  (forall b, List.In b cls -> class_value f b = (c b)%:E) ->
  \int[K w]_z f z = (rsum cls (fun b => c b * rv a b)%R)%:E.
Proof.
move=> ha hw hf f0 hc.
rewrite (@integral_classes D FD V (K w) f hf f0) -lsum_e_EFin.
apply: lsum_e_ext => b hb; rewrite hc // EFinM.
by rewrite -(rvE ha hb hw).
Qed.

Lemma class_value_real (f : Valuation -> \bar real) b :
  finv V f -> List.In b cls -> (forall v, 0 <= f v <= 1) ->
  class_value f b = (fine (class_value f b))%:E.
Proof.
move=> hf hb h01; have [z hz] := class_witness hb.
rewrite (class_valueE hf hb hz); symmetry; apply: fineK.
have /andP [h0 h1] := h01 z.
by rewrite ge0_fin_numE // (le_lt_trans h1) // ltry.
Qed.

Lemma guard_true w a : List.In a cls -> List.In a live_cls ->
  satisfies w (class_formula a) -> cformula_eval_bool beta w = true.
Proof.
move=> ha hl hw; apply/cformula_eval_bool_spec.
move: hl; rewrite List.filter_In => -[_ /liveP hl]; exact: hl.
Qed.

Lemma live_in a : List.In a live_cls -> List.In a cls.
Proof. by rewrite List.filter_In => -[]. Qed.

(** The indicator of exiting into [gamma], class by class. *)
Definition cE b : R := fine (class_value (fun z => (\1_Ex z)%:E) b).

Lemma finv_Ex : finv V (fun z => (\1_Ex z : real)%:E).
Proof.
move=> w w' h; congr (_%:E).
exact: (indic_vinv vEx h).
Qed.

Lemma cE_live b : List.In b cls -> liveb b = true -> cE b = 0%R.
Proof.
move=> hb hl; have [z hz] := class_witness hb.
rewrite /cE (class_valueE finv_Ex hb hz) indicE memNset //=.
move=> hE; have [hnb _] := proj1 (satisfies_and z (c_not beta) gamma) hE; apply: hnb.
by move: hl => /liveP; apply.
Qed.

Lemma W_exit z : cformula_eval_bool beta z = false -> W z Gam = (\1_Gam z)%:E.
Proof.
move=> hz; change (loop beta K z Gam = (\1_Gam z)%:E).
by rewrite loop_unfold hz diracE indicE.
Qed.

Lemma indic_Ex_exit z : cformula_eval_bool beta z = false -> (\1_Ex z : real) = \1_Gam z.
Proof.
move=> hz; have hnb : ~ satisfies z beta by exact/cformula_eval_bool_false.
rewrite !indicP.
destruct (pselect (Ex z)) as [h|h]; destruct (pselect (Gam z)) as [h'|h'] => //; exfalso.
- by apply: h'; have [_ h''] := proj1 (satisfies_and z (c_not beta) gamma) h.
- by apply: h; apply: (proj2 (satisfies_and z (c_not beta) gamma)); split.
Qed.

Lemma cE_dead b : List.In b cls -> liveb b = false -> cE b = xv b.
Proof.
move=> hb hl; have [z hz] := class_witness hb.
have hz' : cformula_eval_bool beta z = false.
  by apply/cformula_eval_bool_false; exact: dead_not_beta hb hl hz.
have e1 : (xv b)%:E = (\1_Gam z)%:E by rewrite (xvE hb hz) W_exit.
have e2 := class_valueE finv_Ex hb hz.
rewrite /cE e2 /= indic_Ex_exit //.
by apply: EFin_inj; rewrite e1.
Qed.

(** On a class outside the guard the loop exits at once. *)
Lemma xv_dead_in a : List.In a cls -> liveb a = false ->
  (forall w, satisfies w (class_formula a) -> satisfies w gamma) -> xv a = 1%R.
Proof.
move=> ha hl hg; have [w hw] := class_witness ha.
have hw' : cformula_eval_bool beta w = false.
  by apply/cformula_eval_bool_false; exact: dead_not_beta ha hl hw.
by apply: EFin_inj; rewrite (xvE ha hw) W_exit // indicE mem_set //; exact: hg.
Qed.

Lemma xv_dead_out a : List.In a cls -> liveb a = false ->
  (forall w, satisfies w (class_formula a) -> ~ satisfies w gamma) -> xv a = 0%R.
Proof.
move=> ha hl hg; have [w hw] := class_witness ha.
have hw' : cformula_eval_bool beta w = false.
  by apply/cformula_eval_bool_false; exact: dead_not_beta ha hl hw.
by apply: EFin_inj; rewrite (xvE ha hw) W_exit // indicE memNset //; exact: hg.
Qed.

(** ** The exit equation *)

Lemma rsum_split_live (f : Assignment -> R) :
  rsum cls f = (rsum live_cls f + rsum dead_cls f)%R.
Proof. exact: rsum_filter. Qed.

Theorem exit_equation a : List.In a live_cls ->
  xv a = (rsum live_cls (fun b => rv a b * xv b) + ev a)%R.
Proof.
move=> hl; have ha := live_in hl; have [w hw] := class_witness ha.
have hbw := guard_true ha hl hw.
have hfW := @finv_kernel D beta gamma body _ _ kinvW vGam.
have hcW : forall b, List.In b cls ->
    class_value (fun z => W z Gam) b = (xv b)%:E.
  by move=> b hb; have [z hz] := class_witness hb; rewrite (class_valueE hfW hb hz) (xvE hb hz).
have hind01 : forall v, 0 <= (\1_Ex v : real)%:E <= 1.
  by move=> v; rewrite !lee_fin; apply/andP; split; [| rewrite indicE; case: (_ \in _)].
have hcE : forall b, List.In b cls ->
    class_value (fun z => (\1_Ex z : real)%:E) b = (cE b)%:E.
  by move=> b hb; rewrite /cE; apply: class_value_real => //; exact: finv_Ex.
have hW : (xv a)%:E = (rsum cls (fun b => xv b * rv a b)%R)%:E.
  rewrite (xvE ha hw).
  change (loop beta K w Gam = (rsum cls (fun b => xv b * rv a b)%R)%:E).
  rewrite loop_unfold hbw.
  exact: (integral_step ha hw hfW (fun v => measure_ge0 _ _) hcW).
have hE : (ev a)%:E = (rsum cls (fun b => cE b * rv a b)%R)%:E.
  have eI : K w Ex = \int[K w]_z (\1_Ex z : real)%:E.
    by rewrite integral_indic ?setIT //; exact: all_measurable.
  rewrite (evE ha hw) eI.
  exact: (integral_step ha hw finv_Ex (fun v => proj1 (andP (hind01 v))) hcE).
have hW' := EFin_inj hW; have hE' := EFin_inj hE.
rewrite hW' hE' !rsum_split_live.
have -> : rsum live_cls (fun b => cE b * rv a b)%R = 0%R.
  apply: rsum_zero => b hb; rewrite cE_live ?mul0r //; first exact: live_in.
  by move: hb; rewrite List.filter_In => -[].
have -> : rsum dead_cls (fun b => cE b * rv a b)%R = rsum dead_cls (fun b => xv b * rv a b)%R.
  apply: rsum_ext => b hb; move: hb; rewrite List.filter_In => -[hb hd].
  by rewrite cE_dead //; move: hd; case: (liveb b).
have -> : rsum live_cls (fun b => xv b * rv a b)%R = rsum live_cls (fun b => rv a b * xv b)%R.
  by apply: rsum_ext => b _; rewrite mulrC.
by rewrite add0r.
Qed.

(** ** Exit layers *)

Local Notation exitk n := (loop_exit beta K n).

Lemma exit0_point z : exitk 0 z Gam = (\1_Ex z : real)%:E.
Proof.
rewrite loop_exit0; destruct (cformula_eval_bool beta z) eqn:hz.
- rewrite indicP; destruct (pselect (Ex z)) as [h|h] => //; exfalso.
  have [hnb _] := proj1 (satisfies_and z (c_not beta) gamma) h.
  by apply: hnb; exact/cformula_eval_bool_spec.
- by rewrite diracE -indicE indic_Ex_exit.
Qed.

Lemma en_ge0 n a : List.In a cls -> (0 <= en n a)%R.
Proof.
move=> ha; have [w hw] := class_witness ha.
by rewrite -lee_fin (enE n ha hw) measure_ge0.
Qed.

Lemma en0 a : List.In a live_cls -> en 0 a = 0%R.
Proof.
move=> hl; have ha := live_in hl; have [w hw] := class_witness ha.
apply: EFin_inj; rewrite (enE 0 ha hw) loop_exit0 (guard_true ha hl hw); reflexivity.
Qed.

Lemma en1 a : List.In a live_cls -> en 1 a = ev a.
Proof.
move=> hl; have ha := live_in hl; have [w hw] := class_witness ha.
apply: EFin_inj; rewrite (enE 1 ha hw) (evE ha hw) loop_exitS (guard_true ha hl hw).
under eq_integral do rewrite exit0_point.
by rewrite integral_indic ?setIT //; exact: all_measurable.
Qed.

Lemma en_dead n b : List.In b cls -> liveb b = false -> en n.+1 b = 0%R.
Proof.
move=> hb hl; have [z hz] := class_witness hb.
have hz' : cformula_eval_bool beta z = false.
  by apply/cformula_eval_bool_false; exact: dead_not_beta hb hl hz.
by apply: EFin_inj; rewrite (enE n.+1 hb hz) loop_exitS hz'.
Qed.

Lemma enSS n a : List.In a live_cls ->
  en n.+2 a = rsum live_cls (fun b => rv a b * en n.+1 b)%R.
Proof.
move=> hl; have ha := live_in hl; have [w hw] := class_witness ha.
have hf := @finv_kernel D beta gamma body _ _ (@kinv_exit D FD beta gamma body n.+1) vGam.
have hc : forall b, List.In b cls ->
    class_value (fun z => exitk n.+1 z Gam) b = (en n.+1 b)%:E.
  by move=> b hb; have [z hz] := class_witness hb; rewrite (class_valueE hf hb hz) (enE n.+1 hb hz).
have e : (en n.+2 a)%:E = (rsum cls (fun b => en n.+1 b * rv a b)%R)%:E.
  rewrite (enE n.+2 ha hw) loop_exitS (guard_true ha hl hw).
  exact: (integral_step ha hw hf (fun v => measure_ge0 _ _) hc).
rewrite (EFin_inj e) rsum_split_live.
have -> : rsum dead_cls (fun b => en n.+1 b * rv a b)%R = 0%R.
  apply: rsum_zero => b hb; move: hb; rewrite List.filter_In => -[hb hd].
  by rewrite en_dead ?mul0r //; move: hd; case: (liveb b).
have -> : rsum live_cls (fun b => en n.+1 b * rv a b)%R = rsum live_cls (fun b => rv a b * en n.+1 b)%R.
  by apply: rsum_ext => b _; rewrite mulrC.
by rewrite addr0.
Qed.

Lemma exit_le_loop n (w : Valuation) A : exitk n w A <= loop beta K w A.
Proof.
have mA : measurable A by exact: all_measurable.
apply: (@le_trans _ _ (loop_approx beta K n w A)).
  rewrite loop_approx_sum // big_ord_recr /=.
  by apply: leeDr; apply: sume_ge0 => i _; exact: measure_ge0.
rewrite loop_approx_sum // loop_event.
have -> : (\sum_(i < n.+1) exitk i w A) = \sum_(0 <= i < n.+1) exitk i w A by rewrite big_mkord.
by apply: nneseries_lim_ge => i _ _; exact: measure_ge0.
Qed.

Lemma en_le_xv n a : List.In a cls -> (en n a <= xv a)%R.
Proof.
move=> ha; have [w hw] := class_witness ha.
rewrite -lee_fin (enE n ha hw) (xvE ha hw); exact: exit_le_loop.
Qed.

Lemma xv_pos_layer a : List.In a cls -> (0 < xv a)%R -> exists n, (0 < en n a)%R.
Proof.
move=> ha hx; have [w hw] := class_witness ha.
case: (pselect (exists n, (0 < en n a)%R)) => // hno; exfalso.
have hz : forall n, exitk n w Gam = 0.
  move=> n; rewrite -(enE n ha hw); congr (_%:E).
  apply/eqP; rewrite eq_le en_ge0 // andbT leNgt; apply/negP => h; apply: hno; by exists n.
have : (xv a)%:E = 0.
  rewrite (xvE ha hw); change (loop beta K w Gam = 0); rewrite loop_event.
  by rewrite eseries0 // => n _ _; exact: hz.
move=> e0; have h0 := EFin_inj e0; by move: hx; rewrite h0 ltxx.
Qed.

End LoopEquations.
