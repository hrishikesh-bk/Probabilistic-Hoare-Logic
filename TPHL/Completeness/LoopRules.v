(** Per-class derivations for a loop (App. D, proof of Lemma 25, (16)-(21)):
    for every class [a] of the loop variables,
      |- {Box gamma_a /\ Pr(tt) = y} while beta do body {Pr(gamma) = x_a * y}.
    Classes outside the guard use [W~]; classes inside it use [W^UB] over all
    live classes and [W^LB] over the live classes with [x_a > 0], ordered by
    the number of iterations needed to exit with positive probability.  The
    body triples come from completeness for the body (the induction
    hypothesis). *)
From Stdlib Require Import Reals List Lra Lia Permutation Sorting.Sorted.
From mathcomp Require boolp ssrbool Rstruct.
Require Import MeasureIntegration PHL.
Require Import Soundness.StateFacts Soundness.AssertionFacts Soundness.SplitRules
  Soundness.LowerCertificate.
Require Import Completeness.FiniteDomain Completeness.Dependence Completeness.LoopClasses
  Completeness.LoopEquations Completeness.LoopOrder Completeness.StructuralRules.
Import ListNotations.

Local Open Scope R_scope.

Section LoopRules.
Context {D : Domain} (FD : FiniteDomain D).
Variables (beta gamma : CFormula D) (body : Cmd D).
Hypothesis body_complete :
  forall pre post, hoare_valid pre body post -> hoare_derivable pre body post.

Local Notation W := (loop_cmd beta body).
Local Notation V := (loop_vars beta gamma body).
Local Notation cls := (cls FD beta gamma body).
Local Notation live_cls := (live_cls FD beta gamma body).
Local Notation liveb := (liveb FD beta).
Local Notation xv := (xv FD beta gamma body).
Local Notation rv := (rv FD body).
Local Notation ev := (ev FD beta gamma body).
Local Notation en := (en FD beta gamma body).
Local Notation Gf a := (class_formula FD a).
Local Notation dflt := (@nil (Var * Val D)).

(** ** Stdlib-facing forms of the semantic facts *)

Definition Rle_of (x y : R) := ssrbool.elimT (@Rstruct.RleP x y).

Lemma xv_ge0 a : In a cls -> 0 <= xv a.
Proof. intros ha. pose proof (xv_bounds ha) as H. apply andb_prop in H. apply Rle_of, H. Qed.

Lemma xv_le1 a : In a cls -> xv a <= 1.
Proof. intros ha. pose proof (xv_bounds ha) as H. apply andb_prop in H. apply Rle_of, H. Qed.

Lemma rv_nonneg a b : In a cls -> In b cls -> 0 <= rv a b.
Proof. intros ha hb. apply Rle_of. exact (rv_ge0 ha hb). Qed.

Lemma ev_nonneg a : In a cls -> 0 <= ev a.
Proof. intros ha. apply Rle_of. exact (ev_ge0 ha). Qed.

Lemma en_nonneg n a : In a cls -> 0 <= en n a.
Proof. intros ha. apply Rle_of. exact (en_ge0 n ha). Qed.

Lemma en_le_x n a : In a cls -> en n a <= xv a.
Proof. intros ha. apply Rle_of. exact (en_le_xv n ha). Qed.

Lemma exit_eq a : In a live_cls ->
  xv a = rsum live_cls (fun b => rv a b * xv b) + ev a.
Proof. intros hl. exact (exit_equation hl). Qed.

Lemma xv_in_R a : In a cls -> liveb a = false ->
  (forall w, satisfies w (Gf a) -> satisfies w gamma) -> xv a = 1.
Proof. intros ha hl hg. exact (xv_dead_in ha hl hg). Qed.

Lemma xv_out_R a : In a cls -> liveb a = false ->
  (forall w, satisfies w (Gf a) -> ~ satisfies w gamma) -> xv a = 0.
Proof. intros ha hl hg. exact (xv_dead_out ha hl hg). Qed.

Lemma en0_R a : In a live_cls -> en 0 a = 0.
Proof. intros hl. exact (en0 hl). Qed.

Lemma enSS_R n a : In a live_cls -> en (S (S n)) a = rsum live_cls (fun b => rv a b * en (S n) b).
Proof. intros hl. exact (enSS n hl). Qed.

Lemma pos_layer a : In a cls -> 0 < xv a -> exists n, 0 < en n a.
Proof.
  intros ha hx.
  destruct (xv_pos_layer ha (ssrbool.introT (@Rstruct.RltP 0 (xv a)) hx)) as [n hn].
  exists n. exact (ssrbool.elimT (@Rstruct.RltP _ _) hn).
Qed.

Lemma body_exact a b ps : In a cls -> In b cls -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (Gf a)) ->
  measure_of (pstate_measure (CommandSemantics.run body ps)) (formula_assertion (Gf b)) =
  rv a b * measure_of (pstate_measure ps) (formula_assertion (Gf a)).
Proof. intros ha hb hps H. exact (body_concentrated ha (vinv_G hb) hps H). Qed.

Lemma body_exact_exit a ps : In a cls -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (Gf a)) ->
  measure_of (pstate_measure (CommandSemantics.run body ps))
    (formula_assertion (c_and (c_not beta) gamma)) =
  ev a * measure_of (pstate_measure ps) (formula_assertion (Gf a)).
Proof. intros ha hps H. exact (body_concentrated ha (@vinv_Ex D beta gamma body) hps H). Qed.

Lemma live_cls_in a : In a live_cls -> In a cls.
Proof. intros h. apply filter_In in h. tauto. Qed.

Lemma live_members a w : In a live_cls -> satisfies w (Gf a) -> satisfies w beta.
Proof.
  intros h hw. apply filter_In in h. destruct h as [_ h].
  apply (proj1 (liveP FD beta a)) in h. exact (h w hw).
Qed.

Lemma live_cls_nodup : NoDup live_cls.
Proof. apply NoDup_filter, classes_nodup. Qed.

Lemma own_class_live w : satisfies w beta ->
  In (assignment_of V w) live_cls.
Proof.
  intros hb. apply filter_In. split; [apply classes_own|].
  apply (proj2 (liveP FD beta _)). intros w' hw'.
  pose proof (classes_own FD V w) as ho.
  apply (proj1 (satisfies_agree V beta w w' (@incl_beta D beta gamma body)
           (classes_agree FD V _ w w' ho (satisfies_own_class FD V w) hw'))).
  exact hb.
Qed.

Lemma class_mass_one (ps : Pstate D) a :
  psatisfies ps (p_concentrated_unit (Gf a)) ->
  psatisfies ps (p_almost_sure (Gf a)) /\
  measure_of (pstate_measure ps) (formula_assertion (Gf a)) = 1.
Proof.
  intros H. apply psatisfies_and in H. destruct H as [H1 H2].
  apply psatisfies_eq in H2. split; [exact H1|].
  apply psatisfies_almost_sure in H1. cbn in H2. rewrite H1. exact H2.
Qed.

(** ** Body triples over a list of regions *)

Section Regions.
Variable L : list (@Assignment D).
Hypothesis L_cls : incl L cls.

Definition reg j := Gf (nth j L dflt).
Definition trans i j := rv (nth i L dflt) (nth j L dflt).
Definition exits i := ev (nth i L dflt).
Definition sol i := xv (nth i L dflt).

Lemma nth_cls i : (i < length L)%nat -> In (nth i L dflt) cls.
Proof. intros h. apply L_cls, nth_In, h. Qed.

Lemma body_valid_upper i : (i < length L)%nat ->
  hoare_valid (p_concentrated_unit (reg i)) body
    (while_body_post_upper (length L) reg (trans i) beta gamma (exits i)).
Proof.
  intros hi ps hps Hpre. destruct (class_mass_one ps _ Hpre) as [Has H1].
  apply psatisfies_and. split.
  - apply finite_p_and_spec. intros j hj. cbn [psatisfies pterm_eval]; unfold reg.
    rewrite (body_exact _ _ ps (nth_cls i hi) (nth_cls j hj) hps Has), H1.
    unfold trans. lra.
  - cbn [psatisfies pterm_eval]; unfold reg.
    rewrite (body_exact_exit _ ps (nth_cls i hi) hps Has), H1. unfold exits. lra.
Qed.

Lemma body_valid_lower i : (i < length L)%nat ->
  hoare_valid (p_concentrated_unit (reg i)) body
    (while_body_post_lower (length L) reg (trans i) beta gamma (exits i)).
Proof.
  intros hi ps hps Hpre. destruct (class_mass_one ps _ Hpre) as [Has H1].
  apply psatisfies_and. split.
  - apply finite_p_and_spec. intros j hj. cbn [psatisfies pterm_eval]; unfold reg.
    rewrite (body_exact _ _ ps (nth_cls i hi) (nth_cls j hj) hps Has), H1.
    unfold trans. lra.
  - cbn [psatisfies pterm_eval]; unfold reg.
    rewrite (body_exact_exit _ ps (nth_cls i hi) hps Has), H1. unfold exits. lra.
Qed.

End Regions.

(** ** Measure facts used in the consequence steps *)

Lemma mass_eq_class ps a (g : CFormula D) :
  (forall w, satisfies w (Gf a) -> satisfies w g) ->
  measure_of (pstate_measure ps) (formula_assertion (c_and g (Gf a))) =
  measure_of (pstate_measure ps) (formula_assertion (Gf a)).
Proof.
  intros h. apply measure_extensional. intros v. unfold formula_assertion.
  rewrite satisfies_and. split; [tauto | intros hv; split; [apply h|]; exact hv].
Qed.

Lemma mass_true ps : measure_of (pstate_measure ps) (formula_assertion (D := D) c_true) =
  measure_of (pstate_measure ps) (fun _ => True).
Proof. apply measure_extensional. intros v. split; [tauto | intros _; apply satisfies_true]. Qed.

Lemma mass_le_true ps (A : Assertion D) : pstate_admissible ps ->
  measure_of (pstate_measure ps) A <= measure_of (pstate_measure ps) (formula_assertion (D := D) c_true).
Proof. intros h. apply measure_of_monotone; [exact h | intros v _; apply satisfies_true]. Qed.

(** ** Classes outside the guard *)

Lemma per_class_dead a y : In a cls -> liveb a = false ->
  hoare_derivable (p_and (p_almost_sure (Gf a)) (p_eq (PProb c_true) (PVar y))) W
    (p_eq (PProb gamma) (PMul (PConst (xv a)) (PVar y))).
Proof.
  intros ha hl.
  assert (hnb : forall w, satisfies w (Gf a) -> ~ satisfies w beta)
    by (intros w hw; exact (dead_not_beta ha hl hw)).
  eapply derive_post; [eapply derive_pre; [| apply (HWhileNot beta (Gf a) body y)] |].
  - intros ps hps H. apply psatisfies_and in H. destruct H as [HG Hy].
    apply psatisfies_and. split; [|exact Hy].
    apply psatisfies_almost_sure. apply psatisfies_almost_sure in HG.
    rewrite (mass_eq_class ps a (c_not beta)); [exact HG|].
    intros w hw. exact (hnb w hw).
  - intros ps hps H. apply psatisfies_and in H. destruct H as [HG Hy].
    apply psatisfies_eq in HG, Hy. apply psatisfies_eq. cbn [pterm_eval] in *.
    pose proof (mass_le_true _ (formula_assertion gamma) hps) as Hle.
    destruct (class_decides (@incl_gamma D beta gamma body) ha) as [hin | hout].
    + rewrite (xv_in_R a ha hl hin).
      assert (measure_of (pstate_measure ps) (formula_assertion (Gf a)) <=
              measure_of (pstate_measure ps) (formula_assertion gamma)).
      { apply measure_of_monotone; [exact hps | exact hin]. }
      lra.
    + rewrite (xv_out_R a ha hl hout).
      pose proof (measure_additive (pstate_measure ps)
                    (formula_assertion gamma) (formula_assertion (Gf a))
                    (ConcreteMeasure.subprob_finite hps)
                    (fun v '(conj h1 h2) => hout v h2 h1)) as Hadd.
      pose proof (mass_le_true _ (fun v => formula_assertion gamma v \/ formula_assertion (Gf a) v) hps).
      pose proof (measure_nonnegative (pstate_measure ps) (formula_assertion gamma)).
      lra.
Qed.

(** ** Classes inside the guard *)

Lemma in_nth_index (L : list (@Assignment D)) a :
  In a L -> exists k, (k < length L)%nat /\ nth k L dflt = a.
Proof. intros h. apply In_nth; exact h. Qed.

Lemma upper_solution :
  while_upper_solution (length live_cls) (sol live_cls) (trans live_cls) (exits live_cls).
Proof.
  intros i hi. set (b := nth i live_cls dflt).
  assert (hb : In b live_cls) by (apply nth_In; exact hi).
  pose proof (xv_ge0 b (live_cls_in b hb)). pose proof (xv_le1 b (live_cls_in b hb)).
  unfold sol, trans, exits. fold b.
  rewrite (finite_r_sum_nth live_cls (fun c => rv b c * xv c) dflt).
  rewrite <- (exit_eq b hb). lra.
Qed.

Lemma upper_cover : while_regions_cover (length live_cls) beta (reg live_cls).
Proof.
  intros w hb. apply satisfies_finite_c_or.
  destruct (in_nth_index live_cls _ (own_class_live w hb)) as [j [hj hjw]].
  exists j. split; [exact hj|]. unfold reg. rewrite hjw. apply satisfies_own_class.
Qed.

Lemma per_class_upper a y : In a live_cls ->
  hoare_derivable (p_and (p_almost_sure (Gf a)) (p_eq (PProb c_true) (PVar y))) W
    (PFLe (PProb gamma) (PMul (PConst (xv a)) (PVar y))).
Proof.
  intros hl. destruct (in_nth_index live_cls a hl) as [k [hk hka]].
  assert (HU := HWhileUpper (length live_cls) k beta gamma body (reg live_cls)
                  (sol live_cls) (exits live_cls) (trans live_cls) y hk upper_cover
                  (fun i hi => body_complete _ _
                     (body_valid_upper live_cls (fun b hb => live_cls_in b hb) i hi))
                  upper_solution).
  unfold sol, reg in HU. rewrite hka in HU.
  eapply derive_pre; [| exact HU].
  intros ps hps H. apply psatisfies_and in H. destruct H as [HG Hy].
  apply psatisfies_almost_sure in HG. apply psatisfies_eq in Hy.
  apply psatisfies_and. split.
  - apply psatisfies_almost_sure. rewrite (mass_eq_class ps a beta); [exact HG|].
    intros w hw; exact (live_members a w hl hw).
  - cbn [psatisfies pterm_eval] in *. lra.
Qed.

(** The number of iterations after which a class first exits with positive
    probability. *)
Definition dkey (b : @Assignment D) : nat :=
  match boolp.pselect (exists n, 0 < en n b) with
  | left H => proj1_sig (boolp.cid (exists_least _ H))
  | right _ => 0
  end.

Lemma dkey_spec b : (exists n, 0 < en n b) ->
  0 < en (dkey b) b /\ forall j, (j < dkey b)%nat -> ~ 0 < en j b.
Proof.
  intros H. unfold dkey. destruct (boolp.pselect _) as [H'|n]; [|contradiction].
  destruct (boolp.cid _) as [m [hm hmin]]. cbn. split; assumption.
Qed.

Definition posb (b : @Assignment D) : bool := if Rlt_dec 0 (xv b) then true else false.
Definition pos_cls : list (@Assignment D) := filter posb live_cls.
Definition ord_cls : list (@Assignment D) := sortk dkey pos_cls.

Lemma ord_perm : Permutation ord_cls pos_cls.
Proof. apply sortk_perm. Qed.

Lemma ord_in b : In b ord_cls <-> In b live_cls /\ 0 < xv b.
Proof.
  split.
  - intros h. apply (Permutation_in _ ord_perm) in h. apply filter_In in h.
    destruct h as [h hp]. unfold posb in hp. destruct (Rlt_dec 0 (xv b)); [|discriminate].
    split; assumption.
  - intros [h hp]. apply (Permutation_in _ (Permutation_sym ord_perm)). apply filter_In.
    split; [exact h|]. unfold posb. destruct (Rlt_dec 0 (xv b)); [reflexivity | contradiction].
Qed.

Lemma ord_nodup : NoDup ord_cls.
Proof.
  apply (Permutation_NoDup (Permutation_sym ord_perm)). apply NoDup_filter, live_cls_nodup.
Qed.

Lemma ord_live b : In b ord_cls -> In b live_cls.
Proof. intros h. apply ord_in in h. tauto. Qed.

Lemma lower_solution :
  while_lower_solution (length ord_cls) (sol ord_cls) (trans ord_cls) (exits ord_cls).
Proof.
  intros i hi. set (b := nth i ord_cls dflt).
  assert (hb : In b ord_cls) by (apply nth_In; exact hi).
  pose proof (ord_live b hb) as hbl.
  pose proof (xv_ge0 b (live_cls_in b hbl)). pose proof (xv_le1 b (live_cls_in b hbl)).
  unfold sol, trans, exits. fold b.
  rewrite (finite_r_sum_nth ord_cls (fun c => rv b c * xv c) dflt).
  rewrite (rsum_perm _ _ (fun c => rv b c * xv c) ord_perm).
  assert (Hs : rsum live_cls (fun c => rv b c * xv c) = rsum pos_cls (fun c => rv b c * xv c)).
  { rewrite (rsum_filter posb live_cls). unfold pos_cls.
    rewrite (rsum_zero (filter (fun x => negb (posb x)) live_cls)); [lra|].
    intros c hc. apply filter_In in hc. destruct hc as [hc hn].
    unfold posb in hn. destruct (Rlt_dec 0 (xv c)) as [|hle]; [discriminate|].
    pose proof (xv_ge0 c (live_cls_in c hc)).
    replace (xv c) with 0 by lra. ring. }
  rewrite <- Hs, <- (exit_eq b hbl). lra.
Qed.

Lemma lower_in_guard : while_regions_in_guard (length ord_cls) beta (reg ord_cls).
Proof.
  intros i hi w hw. apply (live_members (nth i ord_cls dflt) w); [|exact hw].
  apply ord_live, nth_In, hi.
Qed.

Lemma lower_disjoint : while_regions_disjoint (length ord_cls) (reg ord_cls).
Proof.
  intros i j hi hj w hw. apply satisfies_and in hw. destruct hw as [hwi hwj].
  unfold reg in hwi, hwj.
  assert (hci : In (nth i ord_cls dflt) cls) by (apply live_cls_in, ord_live, nth_In; exact hi).
  assert (hcj : In (nth j ord_cls dflt) cls) by (apply live_cls_in, ord_live, nth_In; lia).
  pose proof (classes_disjoint FD V _ _ w hci hcj hwi hwj) as heq.
  apply (proj1 (NoDup_nth ord_cls dflt) ord_nodup i j hi ltac:(lia)) in heq. lia.
Qed.

Lemma lower_progress : while_progress (length ord_cls) (trans ord_cls) (exits ord_cls).
Proof.
  intros i hi. set (b := nth i ord_cls dflt).
  assert (hb : In b ord_cls) by (apply nth_In; exact hi).
  destruct (proj1 (ord_in b) hb) as [hbl hbx].
  pose proof (live_cls_in b hbl) as hbc.
  destruct (dkey_spec b (pos_layer b hbc hbx)) as [hpos hmin].
  unfold exits, trans. fold b.
  destruct (dkey b) as [|[|m]] eqn:Hd.
  - rewrite (en0_R b hbl) in hpos. lra.
  - left. rewrite <- (en1 hbl). exact hpos.
  - right. rewrite (enSS_R m b hbl) in hpos.
    destruct (rsum_pos_term live_cls (fun c => rv b c * en (S m) c)) as [c [hc hcpos]];
      [ intros c hc; apply Rmult_le_pos;
        [apply rv_nonneg; [exact hbc | apply live_cls_in, hc] | apply en_nonneg, live_cls_in, hc]
      | exact hpos |].
    pose proof (rv_nonneg b c hbc (live_cls_in c hc)) as hr0.
    pose proof (en_nonneg (S m) c (live_cls_in c hc)) as he0.
    assert (hr : 0 < rv b c) by nra.
    assert (he : 0 < en (S m) c) by nra.
    assert (hcx : 0 < xv c) by (pose proof (en_le_x (S m) c (live_cls_in c hc)); lra).
    assert (hco : In c ord_cls) by (apply ord_in; split; assumption).
    destruct (in_nth_index ord_cls c hco) as [j [hj hjc]].
    exists j. split; [|rewrite hjc; exact hr].
    apply (sorted_index_lt dkey ord_cls dflt i j (sortk_sorted dkey pos_cls) hi hj).
    fold b. rewrite hjc, Hd.
    destruct (dkey_spec c (ex_intro _ (S m) he)) as [_ hminc].
    destruct (Nat.le_gt_cases (dkey c) (S m)) as [hle|hgt]; [lia|].
    exfalso. exact (hminc (S m) hgt he).
Qed.

Lemma per_class_lower a y : In a live_cls -> 0 < xv a ->
  hoare_derivable (p_and (p_almost_sure (Gf a)) (p_eq (PProb c_true) (PVar y))) W
    (PFLe (PMul (PConst (xv a)) (PVar y)) (PProb gamma)).
Proof.
  intros hl hx.
  assert (ho : In a ord_cls) by (apply ord_in; split; assumption).
  destruct (in_nth_index ord_cls a ho) as [k [hk hka]].
  assert (HL := HWhileLower (length ord_cls) k beta gamma body (reg ord_cls)
                  (sol ord_cls) (exits ord_cls) (trans ord_cls) y hk
                  lower_in_guard lower_disjoint lower_progress
                  (fun i hi => body_complete _ _
                     (body_valid_lower ord_cls (fun b hb => live_cls_in b (ord_live b hb)) i hi))
                  lower_solution).
  unfold sol, reg in HL. rewrite hka in HL.
  eapply derive_pre; [| exact HL].
  intros ps hps H. apply psatisfies_and in H. destruct H as [HG Hy].
  apply psatisfies_almost_sure in HG. apply psatisfies_eq in Hy.
  apply psatisfies_and. split.
  - apply psatisfies_almost_sure. rewrite (mass_eq_class ps a beta); [exact HG|].
    intros w hw; exact (live_members a w hl hw).
  - cbn [psatisfies pterm_eval] in *. lra.
Qed.

Lemma per_class_live a y : In a live_cls ->
  hoare_derivable (p_and (p_almost_sure (Gf a)) (p_eq (PProb c_true) (PVar y))) W
    (p_eq (PProb gamma) (PMul (PConst (xv a)) (PVar y))).
Proof.
  intros hl.
  destruct (Rlt_dec 0 (xv a)) as [hx|hx].
  - eapply derive_post; [apply HAnd; [apply per_class_upper | apply per_class_lower]; assumption |].
    intros ps _ H. apply psatisfies_and in H. destruct H as [H1 H2].
    apply psatisfies_eq. cbn [psatisfies pterm_eval] in *. lra.
  - assert (hx0 : xv a = 0) by (pose proof (xv_ge0 a (live_cls_in a hl)); lra).
    eapply derive_post; [apply per_class_upper; exact hl |].
    intros ps hps H. apply psatisfies_eq. cbn [psatisfies pterm_eval] in *.
    rewrite hx0 in *.
    pose proof (measure_nonnegative (pstate_measure ps) (formula_assertion gamma)).
    lra.
Qed.

(** Every class. *)
Theorem per_class a y : In a cls ->
  hoare_derivable (p_and (p_almost_sure (Gf a)) (p_eq (PProb c_true) (PVar y))) W
    (p_eq (PProb gamma) (PMul (PConst (xv a)) (PVar y))).
Proof.
  intros ha. destruct (liveb a) eqn:hl.
  - apply per_class_live. apply filter_In. split; assumption.
  - apply per_class_dead; assumption.
Qed.

End LoopRules.
