(** Sensor fusion through independent geometric noisy relays.

    This file uses the syntactic proof system in TPHL/PHL.v.  Probabilities
    are unnormalised masses; auxiliary mass variables are frozen with
    ELIMV, rather than identifying an input probability with an output one.
    The whole derivation uses PHL rules and rules derived from them; it does
    not invoke hoare_complete or hoare_derivable_sound.  The Freshness and
    StructuralRules imports below provide only syntactic utilities and
    derived rules, despite their location under Completeness/.
*)
From Stdlib Require Import Reals Lra Psatz Lia List Bool String.
Require Import MeasureIntegration PHL Soundness.StateFacts Soundness.AssertionFacts
  Soundness.SplitRules Soundness.TransformerAssertions
  Completeness.Freshness Completeness.StructuralRules.
Import ListNotations.
Open Scope R_scope.
Open Scope string_scope.

Module SensorFusion.

Section ProbabilityFacts.
Context {D : Domain}.

Definition mass (ps : Pstate D) (g : CFormula D) : R :=
  pterm_eval (PProb g) ps.

Lemma mass_ext ps g h :
  (forall w, satisfies w g <-> satisfies w h) -> mass ps g = mass ps h.
Proof. apply measure_extensional. Qed.

Lemma mass_nonneg ps g : 0 <= mass ps g.
Proof. apply measure_nonnegative. Qed.

Lemma mass_mono ps g h : pstate_admissible ps ->
  (forall w, satisfies w g -> satisfies w h) -> mass ps g <= mass ps h.
Proof. apply measure_of_monotone. Qed.

Lemma mass_true_le ps : pstate_admissible ps -> mass ps c_true <= 1.
Proof.
  intro H. unfold mass; cbn [pterm_eval]. rewrite formula_assertion_true.
  apply measure_subprobability; exact H.
Qed.

Lemma mass_false ps : mass ps FFalse = 0.
Proof. apply measure_empty. Qed.

Lemma mass_split ps g h : pstate_admissible ps ->
  mass ps g = mass ps (c_and h g) + mass ps (c_and (c_not h) g).
Proof.
  intro H. unfold mass; cbn [pterm_eval].
  rewrite <- (measure_additive (pstate_measure ps)
    (formula_assertion (c_and h g))
    (formula_assertion (c_and (c_not h) g))).
  - apply measure_extensional; intro w; unfold formula_assertion.
    rewrite !satisfies_and. destruct (satisfies_dec w h); cbn; tauto.
  - exact (ConcreteMeasure.subprob_finite H).
  - intro w; unfold formula_assertion; rewrite !satisfies_and; cbn; tauto.
Qed.

Lemma mass_on_support ps s g h : pstate_admissible ps ->
  psatisfies ps (p_almost_sure s) ->
  (forall w, satisfies w s -> (satisfies w g <-> satisfies w h)) ->
  mass ps g = mass ps h.
Proof.
  intros Hps Hs Heq. apply psatisfies_almost_sure in Hs.
  pose proof (measure_of_complement_null Hps Hs) as Hz.
  assert (Hnull : forall f, mass ps (c_and (c_not s) f) = 0).
  { intro f. apply (measure_of_null_subset Hps Hz).
    intro w; unfold formula_assertion; rewrite satisfies_and; tauto. }
  rewrite (mass_split ps g s Hps), (mass_split ps h s Hps), !Hnull.
  f_equal. apply mass_ext; intro w; rewrite !satisfies_and.
  split; intros [Hs' Hg]; split; try assumption;
    apply (Heq w Hs'); assumption.
Qed.

Lemma mass_on_unit ps s g (b : bool) : pstate_admissible ps ->
  psatisfies ps (p_concentrated_unit s) ->
  (forall w, satisfies w s -> (satisfies w g <-> b = true)) ->
  mass ps g = if b then 1 else 0.
Proof.
  intros Hps H Heq. apply psatisfies_and in H. destruct H as [Hs Hm].
  apply psatisfies_eq in Hm.
  destruct b.
  - rewrite (mass_on_support ps s g c_true Hps Hs).
    + exact Hm.
    + intros w Hw; specialize (Heq w Hw); cbn; tauto.
  - rewrite (mass_on_support ps s g FFalse Hps Hs).
    + apply mass_false.
    + intros w Hw; specialize (Heq w Hw); cbn in *; intuition discriminate.
Qed.

Definition bit (x : BoolProgramVar) (b : bool) : CFormula D :=
  if b then FProgBool x else c_not (FProgBool x).

Lemma satisfies_bit w x b : satisfies w (bit x b) <-> bool_program_values w x = b.
Proof. destruct b; cbn; destruct (bool_program_values w x); intuition discriminate. Qed.

Lemma bool_update_here (w : state D) x b : bool_program_values (update_bool w x b) x = b.
Proof. cbn; destruct (bool_program_var_eq_dec x x); congruence. Qed.

Lemma bool_update_other (w : state D) x y b : x <> y ->
  bool_program_values (update_bool w x b) y = bool_program_values w y.
Proof. intro H; cbn; destruct (bool_program_var_eq_dec y x); congruence. Qed.

Lemma mass_bit_pair ps C x z : pstate_admissible ps ->
  mass ps (c_and C (bit x z)) + mass ps (c_and C (bit x (negb z))) = mass ps C.
Proof.
  intro Hps. rewrite (mass_split ps C (FProgBool x) Hps) at 1.
  destruct z; cbn [bit negb];
    rewrite (mass_ext ps (c_and (FProgBool x) C) (c_and C (FProgBool x))),
      (mass_ext ps (c_and (c_not (FProgBool x)) C) (c_and C (c_not (FProgBool x))));
    try (intro w; rewrite !satisfies_and; tauto); ring.
Qed.

Lemma assign_support x (value S T : CFormula D) y :
  (forall w, satisfies w S -> satisfies (update_bool w x (cformula_eval_bool value w)) T) ->
  hoare_derivable
    (p_and (p_almost_sure S) (p_eq (PProb c_true) (PVar y)))
    (CBoolAssign x value)
    (p_and (p_almost_sure T) (p_eq (PProb c_true) (PVar y))).
Proof.
  intro H. eapply derive_pre; [|apply HBoolAssign].
  intros ps Hps Hpre. apply psatisfies_and in Hpre; destruct Hpre as [Hs Hm].
  change (psatisfies ps (p_and (p_almost_sure (subst_bool_cformula x value T))
    (p_eq (PProb c_true) (PVar y)))).
  apply psatisfies_and; split; [|exact Hm]. apply psatisfies_almost_sure.
  apply (mass_on_support ps S _ c_true Hps Hs).
  intros w Hw; rewrite subst_bool_cformula_correct; split;
    [intros _; apply satisfies_true|intros _; apply H; exact Hw].
Qed.

End ProbabilityFacts.

(** These two derived rules only use SUM, AND, Pr-FREE, ELIMV and CONS.
    They turn classwise probability equations into equations on a mixture. *)
Section MixtureRules.
Context {D : Domain}.

Lemma scaled_transfer (c : Cmd D) S target k :
  (forall m, hoare_derivable
    (p_and (p_almost_sure S) (p_eq (PProb c_true) (PVar m))) c
    (p_eq (PProb target) (PMul (PConst k) (PVar m)))) ->
  forall y, hoare_derivable
    (p_and (p_eq (PVar y) (PMul (PConst k) (PProb c_true))) (p_almost_sure S)) c
    (p_eq (PVar y) (PProb target)).
Proof.
  intros H y.
  set (m := fresh_prob_logic_var [y]).
  assert (Hym : y <> m).
  { pose proof (fresh_prob_logic_var_not_in [y]); fold m in H0; cbn in H0; tauto. }
  set (frame := p_eq (PVar y) (PMul (PConst k) (PVar m)) : PFormula D).
  assert (HD : hoare_derivable
    (p_and (p_and frame (p_almost_sure S)) (p_eq (PVar m) (PProb c_true))) c
    (p_eq (PVar y) (PProb target))).
  { eapply derive_post with (post := p_and
      (p_eq (PProb target) (PMul (PConst k) (PVar m))) frame).
    - apply HAnd.
      + eapply derive_pre; [|apply H].
        intros ps Hps HP; rewrite !psatisfies_and in HP.
        apply psatisfies_and; split; [tauto|].
        apply psatisfies_eq; destruct HP as [_ HM]; apply psatisfies_eq in HM.
        symmetry; exact HM.
      + eapply derive_pre; [|apply HFree; unfold frame; cbn; tauto].
        intros ps Hps HP; rewrite !psatisfies_and in HP; tauto.
    - intros ps Hps HP; apply psatisfies_and in HP; destruct HP as [HT HF].
      apply psatisfies_eq in HT; unfold frame in HF; apply psatisfies_eq in HF.
      apply psatisfies_eq; cbn [pterm_eval] in *; congruence. }
  pose proof (HElimv (p_and frame (p_almost_sure S)) _ m (PProb c_true) c HD
    ltac:(cbn; tauto) ltac:(cbn; intuition congruence)) as HE.
  unfold frame in HE.
  cbn [subst_prob_pformula subst_prob_pterm p_eq p_and p_not p_almost_sure] in HE.
  destruct (prob_logic_var_eq_dec y m); [contradiction|].
  destruct (prob_logic_var_eq_dec m m); [exact HE|contradiction].
Qed.

Lemma split_transfer (c : Cmd D) S1 S2 target (T1 T2 : Pterm D) :
  (forall z, ~ prob_logic_var_occurs_pterm z T1) ->
  (forall z, ~ prob_logic_var_occurs_pterm z T2) ->
  cformula_valid (c_not (c_and S1 S2)) ->
  (forall y, hoare_derivable (p_and (p_eq (PVar y) T1) (p_almost_sure S1)) c
    (p_eq (PVar y) (PProb target))) ->
  (forall y, hoare_derivable (p_and (p_eq (PVar y) T2) (p_almost_sure S2)) c
    (p_eq (PVar y) (PProb target))) ->
  forall y, hoare_derivable
    (p_and (p_eq (PVar y)
      (PAdd (condition_pterm T1 S1) (condition_pterm T2 S2)))
      (p_almost_sure (c_or S1 S2))) c (p_eq (PVar y) (PProb target)).
Proof.
  intros HT1 HT2 Hdis H1 H2 y.
  set (a := condition_pterm T1 S1).
  set (b := condition_pterm T2 S2).
  assert (Hcond : forall (t : Pterm D) S z,
    ~ prob_logic_var_occurs_pterm z t ->
    ~ prob_logic_var_occurs_pterm z (condition_pterm t S)).
  { intros t S z; induction t; cbn; tauto. }
  assert (Ha : forall z, ~ prob_logic_var_occurs_pterm z a) by (intro; apply Hcond, HT1).
  assert (Hb : forall z, ~ prob_logic_var_occurs_pterm z b) by (intro; apply Hcond, HT2).
  set (u := fresh_prob_logic_var [y]).
  set (v := fresh_prob_logic_var [u;y]).
  assert (Hu : ~ In u [y]) by apply fresh_prob_logic_var_not_in.
  assert (Hv : ~ In v [u;y]) by apply fresh_prob_logic_var_not_in.
  cbn in Hu, Hv.
  assert (Huy : y <> u) by tauto.
  assert (Hvy : y <> v) by tauto.
  assert (Huv : u <> v) by tauto.
  set (frame := p_eq (PVar y) (PAdd (PVar u) (PVar v)) : PFormula D).
  set (base := p_and frame (p_almost_sure (c_or S1 S2))).
  set (bindings := [(u,a);(v,b)]).
  assert (Hind : independent_bindings bindings).
  { split.
    - cbn [bindings map]; repeat constructor; cbn; intuition congruence.
    - intros z r w t Hz Ht; cbn [bindings] in Ht.
      destruct Ht as [Ht | [Ht | Ht]]; try contradiction;
        inversion Ht; subst; [apply Ha|apply Hb]. }
  assert (Hpost : forall z r, In (z,r) bindings ->
    ~ prob_logic_var_occurs_pformula z (p_eq (PVar y) (PProb target))).
  { intros z r Hz; cbn [bindings] in Hz.
    destruct Hz as [Hz | [Hz | Hz]]; try contradiction;
      inversion Hz; subst; cbn; intuition congruence. }
  assert (HD : hoare_derivable (bindings_precondition bindings base) c
    (p_eq (PVar y) (PProb target))).
  { eapply derive_post with (post := p_and
      (p_eq (PAdd (PVar u) (PVar v)) (PProb target)) frame).
    - apply HAnd.
      + eapply derive_pre with (pre' := sum_precondition
          (p_eq (PVar u) T1) (p_eq (PVar v) T2) S1 S2).
        * intros ps Hps HP; cbn [bindings bindings_precondition] in HP; unfold base in HP.
          rewrite !psatisfies_and in HP.
          unfold sum_precondition; rewrite !psatisfies_and.
          change ((psatisfies ps (p_eq (PVar u) a) /\
            psatisfies ps (p_eq (PVar v) b)) /\
            psatisfies ps (p_almost_sure (c_or S1 S2))).
          tauto.
        * apply derive_sum_eq; [exact Hdis|apply H1|apply H2].
      + eapply derive_pre; [|apply HFree; unfold frame; cbn; tauto].
        intros ps Hps HP; cbn [bindings bindings_precondition] in HP; unfold base in HP.
        rewrite !psatisfies_and in HP; tauto.
    - intros ps Hps HP; apply psatisfies_and in HP; destruct HP as [HS HF].
      apply psatisfies_eq in HS; unfold frame in HF; apply psatisfies_eq in HF.
      apply psatisfies_eq; cbn [pterm_eval] in *; congruence. }
  pose proof (derive_eliminate_bindings bindings base _ _ Hind Hpost HD) as HE.
  assert (E : substitute_bindings bindings base =
    p_and (p_eq (PVar y) (PAdd a b)) (p_almost_sure (c_or S1 S2))).
  { unfold bindings, base, frame.
    cbn [substitute_bindings subst_prob_pformula p_eq p_and p_not p_almost_sure subst_prob_pterm].
    repeat match goal with
    | |- context [prob_logic_var_eq_dec ?z ?w] =>
        destruct (prob_logic_var_eq_dec z w); cbn [subst_prob_pterm]
    end; try congruence;
      rewrite (subst_prob_pterm_fresh v b a (Ha v)); reflexivity. }
  rewrite E in HE; exact HE.
Qed.

(** Replace the saved probability variable by an arbitrary analytical
    expression (for example a polynomial in the input marginals). *)
Lemma transfer_analytical (c : Cmd D) target (T t : Pterm D) :
  (forall z, ~ prob_logic_var_occurs_pterm z T) -> pterm_analytical t ->
  (forall y, hoare_derivable (p_eq (PVar y) T) c
    (p_eq (PVar y) (PProb target))) ->
  hoare_derivable (p_eq T t) c (p_eq (PProb target) t).
Proof.
  intros HT Ht H.
  set (y := fresh_prob_logic_var (pterm_prob_vars t)).
  assert (Hy : ~ prob_logic_var_occurs_pterm y t).
  { intro HO; apply pterm_prob_vars_spec in HO.
    exact (fresh_prob_logic_var_not_in _ HO). }
  assert (HD : hoare_derivable
    (p_and (p_eq (PVar y) T) (p_eq (PVar y) t)) c (p_eq (PProb target) t)).
  { eapply derive_post with (post := p_and
      (p_eq (PVar y) (PProb target)) (p_eq (PVar y) t)).
    - apply HAnd.
      + eapply derive_pre; [|apply H].
        intros ps Hps HP; apply psatisfies_and in HP; tauto.
      + eapply derive_pre; [|apply HFree; cbn; tauto].
        intros ps Hps HP; apply psatisfies_and in HP; tauto.
    - intros ps Hps HP; apply psatisfies_and in HP; destruct HP as [H1 H2].
      apply psatisfies_eq in H1, H2; apply psatisfies_eq; congruence. }
  pose proof (HElimv (p_eq (PVar y) T) _ y t c HD Hy ltac:(cbn; tauto)) as HE.
  cbn [subst_prob_pformula p_eq p_and p_not subst_prob_pterm] in HE.
  destruct (prob_logic_var_eq_dec y y); [|contradiction].
  rewrite (subst_prob_pterm_fresh y t T (HT y)) in HE.
  eapply derive_pre; [|exact HE].
  intros ps Hps HP; apply psatisfies_eq in HP; apply psatisfies_eq; symmetry; exact HP.
Qed.

End MixtureRules.

Definition a := bool_program_var "a".
Definition b := bool_program_var "b".
Definition oa := bool_program_var "oa".
Definition ob := bool_program_var "ob".
Definition go := bool_program_var "go".
Definition f := bool_program_var "f".
Definition g := bool_program_var "g".
Definition alarm := bool_program_var "alarm".
Definition alpha := prob_logic_var "alpha".
Definition beta := prob_logic_var "beta".

Definition flip_probability (p d : R) := p / (d + 2*p*(1-d)).

Lemma flip_probability_bounds p d : 0 < p < 1 -> 0 < d <= 1 ->
  0 < flip_probability p d < 1.
Proof.
  intros Hp Hd. assert (Hden : 0 < d + 2*p*(1-d)) by nra.
  unfold flip_probability. split.
  - apply Rdiv_lt_0_compat; lra.
  - apply (Rmult_lt_reg_r (d + 2*p*(1-d))); [exact Hden|].
    field_simplify; nra.
Qed.

Lemma flip_probability_equation p d : 0 < p < 1 -> 0 < d <= 1 ->
  flip_probability p d =
  p + (1-d)*(1-2*p)*flip_probability p d.
Proof.
  intros Hp Hd. assert (Hden : d + 2*p*(1-d) <> 0) by nra.
  unfold flip_probability; field; exact Hden.
Qed.

Section Relay.
Context {D : Domain}.
Variables (out coin : BoolProgramVar) (p d : R).

Definition flip : CFormula D := c_iff (FProgBool out) (c_not (FProgBool coin)).
Definition relay_body : Cmd D :=
  CSeq (CBoolToss coin p)
    (CSeq (CBoolAssign out flip) (CBoolToss go (1-d))).
Definition relay_loop : Cmd D := CWhile (FProgBool go) relay_body.
Definition relay (input : BoolProgramVar) : Cmd D :=
  CSeq (CBoolAssign out (FProgBool input))
    (CSeq (CBoolAssign go c_true) relay_loop).

Definition body_wp (eta : PFormula D) :=
  toss_pformula coin p
    (subst_bool_pformula out flip (toss_pformula go (1-d) eta)).

Lemma body_rule eta : 0 <= p <= 1 -> 0 <= d <= 1 ->
  hoare_derivable (body_wp eta) relay_body eta.
Proof.
  intros Hp Hd. unfold body_wp, relay_body. eapply HSeq.
  - apply HBoolToss; exact Hp.
  - eapply HSeq; [apply HBoolAssign|apply HBoolToss; unfold coin_probability_valid; lra].
Qed.

Definition after_coins (h k : bool) (target : CFormula D) :=
  subst_bool_cformula coin (if h then c_true else FFalse)
    (subst_bool_cformula out flip
      (subst_bool_cformula go (if k then c_true else FFalse) target)).

Definition body_mass (ps : Pstate D) (target : CFormula D) :=
  (1-p)*(d*mass ps (after_coins false false target) +
          (1-d)*mass ps (after_coins false true target)) +
  p*(d*mass ps (after_coins true false target) +
      (1-d)*mass ps (after_coins true true target)).

Lemma body_wp_eq ps target value :
  psatisfies ps (body_wp (p_eq (PProb target) (PConst value))) <->
  body_mass ps target = value.
Proof.
  unfold body_wp.
  change (psatisfies ps (p_eq
    (toss_pterm coin p
      (subst_bool_pterm out flip (toss_pterm go (1-d) (PProb target))))
    (PConst value)) <-> body_mass ps target = value).
  rewrite psatisfies_eq.
  cbn [toss_pterm subst_bool_pterm pterm_eval].
  unfold body_mass, after_coins, mass; cbn [pterm_eval].
  replace (1-(1-d)) with d by ring. split; intro H; nra.
Qed.

Lemma body_exact pre target value : 0 <= p <= 1 -> 0 <= d <= 1 ->
  (forall ps, pstate_admissible ps -> psatisfies ps pre -> body_mass ps target = value) ->
  hoare_derivable pre relay_body (p_eq (PProb target) (PConst value)).
Proof.
  intros Hp Hd H. eapply derive_pre; [|apply body_rule; assumption].
  intros ps Hps Hpre. apply body_wp_eq; apply H; assumption.
Qed.

Lemma flip_eval w : cformula_eval_bool flip w =
  xorb (bool_program_values w out) (bool_program_values w coin).
Proof.
  unfold flip, c_iff, c_and, c_not; cbn [cformula_eval_bool].
  destruct (bool_program_values w out), (bool_program_values w coin); reflexivity.
Qed.

Lemma body_go_rule (support : CFormula D) live : 0 <= p <= 1 -> 0 <= d <= 1 ->
  hoare_derivable (p_concentrated_unit support) relay_body
    (p_eq (PProb (bit go live)) (PConst (if live then 1-d else d))).
Proof.
  intros Hp Hd. apply body_exact; try assumption.
  intros ps Hps H.
  assert (E : forall h k, mass ps (after_coins h k (bit go live)) =
    if Bool.eqb k live then 1 else 0).
  { intros h k. apply (mass_on_unit ps support); try assumption.
    intros w Hw. unfold after_coins.
    rewrite subst_bool_const_correct, subst_bool_cformula_correct,
      subst_bool_const_correct, satisfies_bit, bool_update_here.
    rewrite Bool.eqb_true_iff; reflexivity. }
  unfold body_mass; rewrite !E; destruct live; cbn; ring.
Qed.

Lemma loop_mass_upper y : 0 <= p <= 1 -> 0 <= d <= 1 ->
  hoare_derivable
    (p_and (p_almost_sure (FProgBool go)) (PFLe (PProb c_true) (PVar y)))
    relay_loop (PFLe (PProb c_true) (PVar y)).
Proof.
  intros Hp Hd.
  eapply derive_pre with (pre' := p_and
    (p_almost_sure (c_and (FProgBool go) (FProgBool go)))
    (PFLe (PProb c_true) (PVar y))).
  - intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
    split; [|exact Hm]. apply psatisfies_almost_sure in H.
    apply psatisfies_almost_sure.
    rewrite (measure_extensional _ _ (formula_assertion (FProgBool go))); [exact H|].
    intro w; unfold formula_assertion; rewrite satisfies_and; tauto.
  - eapply derive_post.
    + apply (HWhileUpper 1 0 (FProgBool go) c_true relay_body
        (fun _ => FProgBool go) (fun _ => 1) (fun _ => d)
        (fun _ _ => 1-d) y).
      * lia.
      * intros w H; cbn [finite_c_or]; apply satisfies_or; right; exact H.
      * intros i Hi. unfold while_body_post_upper; cbn [finite_p_and].
        apply HAnd.
        -- apply HAnd; [apply derive_true|].
           eapply derive_post; [apply (body_go_rule (FProgBool go) true); assumption|].
           intros ps Hps H; apply psatisfies_eq in H; cbn in H |- *; lra.
        -- eapply derive_post; [apply (body_go_rule (FProgBool go) false); assumption|].
           intros ps Hps H; apply psatisfies_eq in H.
           change (mass ps (c_and (c_not (FProgBool go)) c_true) <= d).
           rewrite (mass_ext ps _ (c_not (FProgBool go))).
           ++ change (mass ps (c_not (FProgBool go)) = d) in H; lra.
           ++ intro w; rewrite satisfies_and; cbn; tauto.
      * intros i Hi; cbn [finite_r_sum]; split; lra.
    + intros ps Hps H; cbn in H |- *; lra.
Qed.

Lemma relay_mass_upper input y : 0 <= p <= 1 -> 0 <= d <= 1 ->
  hoare_derivable (p_eq (PProb c_true) (PVar y))
    (relay input) (PFLe (PProb c_true) (PVar y)).
Proof.
  intros Hp Hd. unfold relay.
  eapply HSeq with (eta2 := p_eq (PProb c_true) (PVar y)).
  - change (@hoare_derivable D
      (subst_bool_pformula out (FProgBool input) (p_eq (PProb c_true) (PVar y)))
      (CBoolAssign out (FProgBool input)) (p_eq (PProb c_true) (PVar y))).
    apply HBoolAssign.
  - eapply HSeq with (eta2 := p_and (p_almost_sure (FProgBool go))
      (p_eq (PProb c_true) (PVar y))).
    + eapply derive_pre; [|apply (assign_support go c_true c_true (FProgBool go) y)].
      * intros ps Hps H; apply psatisfies_and; split; [|exact H].
        apply psatisfies_almost_sure; reflexivity.
      * intros w _; cbn [cformula_eval_bool]; apply bool_update_here.
    + eapply derive_pre; [|apply loop_mass_upper; assumption].
      intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
      split; [exact H|]. apply psatisfies_eq in Hm; cbn in Hm |- *; lra.
Qed.

Hypotheses (out_coin : out <> coin) (out_go : out <> go) (coin_go : coin <> go).
Variable C : CFormula D.
Hypothesis C_out : forall w z, satisfies (update_bool w out z) C <-> satisfies w C.
Hypothesis C_coin : forall w z, satisfies (update_bool w coin z) C <-> satisfies w C.
Hypothesis C_go : forall w z, satisfies (update_bool w go z) C <-> satisfies w C.

Definition region (z : bool) := c_and (FProgBool go) (c_and C (bit out z)).
Definition outcome (k z : bool) := c_and (bit go k) (c_and C (bit out z)).

Lemma after_outcome w initial h k live z :
  satisfies w (region initial) ->
  (satisfies w (after_coins h k (outcome live z)) <->
    k = live /\ xorb initial h = z).
Proof.
  intro H. unfold region in H; rewrite !satisfies_and, satisfies_bit in H.
  destruct H as [Hgo [HC Ho]].
  unfold after_coins. rewrite subst_bool_const_correct, subst_bool_cformula_correct,
    subst_bool_const_correct, flip_eval.
  rewrite bool_update_other by congruence.
  rewrite bool_update_here, Ho.
  unfold outcome. rewrite !satisfies_and, !satisfies_bit.
  rewrite bool_update_here, bool_update_other by congruence.
  rewrite bool_update_here, C_go, C_out, C_coin. tauto.
Qed.

Definition chance (initial final : bool) := if Bool.eqb initial final then 1-p else p.

Lemma body_outcome ps initial live z : pstate_admissible ps ->
  psatisfies ps (p_concentrated_unit (region initial)) ->
  body_mass ps (outcome live z) =
    (if live then 1-d else d) * chance initial z.
Proof.
  intros Hps H.
  assert (E : forall h k, mass ps (after_coins h k (outcome live z)) =
    if andb (Bool.eqb k live) (Bool.eqb (xorb initial h) z) then 1 else 0).
  { intros h k. apply (mass_on_unit ps (region initial)); try assumption.
    intros w Hw; rewrite (after_outcome w initial h k live z Hw).
    rewrite andb_true_iff, !Bool.eqb_true_iff. reflexivity. }
  unfold body_mass. rewrite !E. unfold chance.
  destruct initial, live, z; cbn; ring.
Qed.

Lemma body_outcome_rule initial live z : 0 <= p <= 1 -> 0 <= d <= 1 ->
  hoare_derivable (p_concentrated_unit (region initial)) relay_body
    (p_eq (PProb (outcome live z))
      (PConst ((if live then 1-d else d) * chance initial z))).
Proof.
  intros Hp Hd. apply body_exact; try assumption.
  intros ps Hps H; apply body_outcome; assumption.
Qed.

Definition index_bit (i : nat) := negb (Nat.eqb i 0).
Definition delivery (initial final : bool) :=
  if Bool.eqb initial final then 1-flip_probability p d else flip_probability p d.

Lemma delivery_equation initial final : 0 < p < 1 -> 0 < d <= 1 ->
  delivery initial final =
    (1-d)*chance initial false*delivery false final +
    (1-d)*chance initial true*delivery true final + d*chance initial final.
Proof.
  intros Hp Hd. pose proof (flip_probability_equation p d Hp Hd) as H.
  unfold delivery, chance; destruct initial, final; cbn; nra.
Qed.

Lemma loop_lower initial final y : 0 < p < 1 -> 0 < d <= 1 ->
  hoare_derivable
    (p_and (p_almost_sure (region initial)) (PFLe (PVar y) (PProb c_true)))
    relay_loop
    (PFLe (PMul (PConst (delivery initial final)) (PVar y))
      (PProb (c_and C (bit out final)))).
Proof.
  intros Hp Hd.
  pose proof (flip_probability_bounds p d Hp Hd) as Hu.
  assert (Hrow : forall (initial live final : bool),
    hoare_derivable (p_concentrated_unit (region initial)) relay_body
      (PFLe (PConst ((if live then 1-d else d)*chance initial final))
        (PProb (outcome live final)))).
  { intros i k z. eapply derive_post; [apply (body_outcome_rule i k z); lra|].
    intros ps Hps H; apply psatisfies_eq in H; cbn in H |- *; lra. }
  eapply derive_pre with (pre' := p_and
    (p_almost_sure (c_and (FProgBool go) (region initial)))
    (PFLe (PVar y) (PProb c_true))).
  - intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
    split; [|exact Hm]. apply psatisfies_almost_sure in H.
    apply psatisfies_almost_sure.
    rewrite (measure_extensional _ _ (formula_assertion (region initial))); [exact H|].
    intro w; unfold formula_assertion, region; rewrite !satisfies_and; tauto.
  - replace initial with (index_bit (if initial then 1 else 0)) at 1 2
      by (destruct initial; reflexivity).
    apply (HWhileLower 2 (if initial then 1 else 0)
      (FProgBool go) (c_and C (bit out final)) relay_body
      (fun i => region (index_bit i))
      (fun i => delivery (index_bit i) final)
      (fun i => d*chance (index_bit i) final)
      (fun i j => (1-d)*chance (index_bit i) (index_bit j)) y).
    + destruct initial; lia.
    + intros i Hi w H; unfold region in H; apply satisfies_and in H; tauto.
    + intros i j Hi Hj w H; apply satisfies_and in H; destruct H as [H1 H2].
      assert (i = 1 /\ j = 0)%nat by lia. destruct H as [-> ->].
      unfold region in H1, H2; rewrite !satisfies_and, satisfies_bit in H1, H2.
      destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
      change (bool_program_values w out = true) in H1.
      change (bool_program_values w out = false) in H2. congruence.
    + intros i Hi; left. unfold chance.
      destruct (Bool.eqb (index_bit i) final); nra.
    + intros i Hi. unfold while_body_post_lower; cbn [finite_p_and].
      apply HAnd.
      * apply HAnd.
        -- apply HAnd; [apply derive_true|exact (Hrow (index_bit i) true false)].
        -- exact (Hrow (index_bit i) true true).
      * exact (Hrow (index_bit i) false final).
    + intros i Hi. cbn [finite_r_sum]. split.
      * change (delivery (index_bit i) final <= 0 + (1-d)*chance (index_bit i) false*delivery false final +
          (1-d)*chance (index_bit i) true*delivery true final +
          d*chance (index_bit i) final).
        pose proof (delivery_equation (index_bit i) final Hp Hd); lra.
      * unfold delivery; destruct (Bool.eqb (index_bit i) final); lra.
Qed.

Lemma loop_exact initial final y : 0 < p < 1 -> 0 < d <= 1 ->
  hoare_derivable
    (p_and (p_almost_sure (region initial)) (p_eq (PProb c_true) (PVar y)))
    relay_loop
    (p_eq (PProb (c_and C (bit out final)))
      (PMul (PConst (delivery initial final)) (PVar y))).
Proof.
  intros Hp Hd.
  eapply derive_post with (post := p_and
    (PFLe (PMul (PConst (delivery initial final)) (PVar y))
      (PProb (c_and C (bit out final))))
    (p_and
      (PFLe (PMul (PConst (delivery initial (negb final))) (PVar y))
        (PProb (c_and C (bit out (negb final)))))
      (PFLe (PProb c_true) (PVar y)))).
  - apply HAnd.
    + eapply derive_pre; [|apply loop_lower; assumption].
      intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
      split; [exact H|]. apply psatisfies_eq in Hm; cbn in Hm |- *; lra.
    + apply HAnd.
      * eapply derive_pre; [|apply loop_lower; assumption].
        intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
        split; [exact H|]. apply psatisfies_eq in Hm; cbn in Hm |- *; lra.
      * eapply derive_pre; [|apply loop_mass_upper; lra].
        intros ps Hps H; rewrite !psatisfies_and in *; destruct H as [H Hm].
        split.
        -- apply psatisfies_almost_sure.
           apply (mass_on_support ps (region initial) _ c_true Hps H).
           intros w Hw. unfold region in Hw; rewrite satisfies_and in Hw.
           split; [intros _; apply satisfies_true|tauto].
        -- apply psatisfies_eq in Hm; cbn in Hm |- *; lra.
  - intros ps Hps H. rewrite !psatisfies_and in H.
    destruct H as [H1 [H2 H3]]. apply psatisfies_eq.
    change (delivery initial final * pstate_prob_logic_values ps y <=
      mass ps (c_and C (bit out final))) in H1.
    change (delivery initial (negb final) * pstate_prob_logic_values ps y <=
      mass ps (c_and C (bit out (negb final)))) in H2.
    change (mass ps c_true <= pstate_prob_logic_values ps y) in H3.
    pose proof (mass_bit_pair ps C out final Hps) as E.
    pose proof (mass_mono ps C c_true Hps (fun w _ => satisfies_true w)) as H4.
    change (mass ps (c_and C (bit out final)) =
      delivery initial final * pstate_prob_logic_values ps y).
    assert (Ec : delivery initial final + delivery initial (negb final) = 1).
    { unfold delivery; destruct initial, final; cbn; ring. }
    nra.
Qed.

Lemma relay_class_exact input initial final y :
  (forall w, satisfies w C -> bool_program_values w input = initial) ->
  0 < p < 1 -> 0 < d <= 1 ->
  hoare_derivable
    (p_and (p_almost_sure C) (p_eq (PProb c_true) (PVar y)))
    (relay input)
    (p_eq (PProb (c_and C (bit out final)))
      (PMul (PConst (delivery initial final)) (PVar y))).
Proof.
  intros HC Hp Hd. unfold relay.
  eapply HSeq with (eta2 := p_and (p_almost_sure (c_and C (bit out initial)))
    (p_eq (PProb c_true) (PVar y))).
  - apply assign_support; intros w Hw. rewrite satisfies_and, satisfies_bit.
    rewrite C_out, bool_update_here. split; [exact Hw|]. cbn; apply HC; exact Hw.
  - eapply HSeq; [|apply loop_exact; assumption].
    apply assign_support. intros w Hw. unfold region; rewrite !satisfies_and.
    rewrite C_go, satisfies_bit, bool_update_other by congruence.
    split; [cbn [cformula_eval_bool]; apply bool_update_here|].
    rewrite satisfies_and, satisfies_bit in Hw; exact Hw.
Qed.

(** The two output classes exhaust the incoming mass.  This retains both
    the stable input class and its mass, without invoking soundness. *)
Lemma relay_class_summary input initial y :
  (forall w, satisfies w C -> bool_program_values w input = initial) ->
  0 < p < 1 -> 0 < d <= 1 ->
  hoare_derivable
    (p_and (p_almost_sure C) (p_eq (PProb c_true) (PVar y)))
    (relay input)
    (p_and (p_almost_sure C)
      (p_and (p_eq (PProb c_true) (PVar y))
        (p_eq (PProb (FProgBool out))
          (PMul (PConst (delivery initial true)) (PVar y))))).
Proof.
  intros HC Hp Hd.
  eapply derive_post with (post := p_and
    (p_eq (PProb (c_and C (bit out true)))
      (PMul (PConst (delivery initial true)) (PVar y)))
    (p_and (p_eq (PProb (c_and C (bit out false)))
      (PMul (PConst (delivery initial false)) (PVar y)))
      (PFLe (PProb c_true) (PVar y)))).
  - apply HAnd; [apply relay_class_exact; assumption|].
    apply HAnd; [apply relay_class_exact; assumption|].
    eapply derive_pre; [|apply relay_mass_upper; lra].
    intros ps Hps H; apply psatisfies_and in H; tauto.
  - intros ps Hps H; rewrite !psatisfies_and in H.
    destruct H as [HT [HF HU]]. apply psatisfies_eq in HT, HF.
    change (mass ps (c_and C (bit out true)) =
      delivery initial true * pstate_prob_logic_values ps y) in HT.
    change (mass ps (c_and C (bit out false)) =
      delivery initial false * pstate_prob_logic_values ps y) in HF.
    change (mass ps c_true <= pstate_prob_logic_values ps y) in HU.
    pose proof (mass_bit_pair ps C out true Hps) as E.
    cbn [negb] in E; rewrite HT, HF in E.
    assert (Ec : delivery initial true + delivery initial false = 1).
    { unfold delivery; destruct initial; cbn; ring. }
    pose proof (mass_mono ps C c_true Hps (fun w _ => satisfies_true w)) as HM.
    assert (HTotal : mass ps c_true = pstate_prob_logic_values ps y) by nra.
    assert (HS : psatisfies ps (p_almost_sure C)).
    { apply psatisfies_almost_sure; change (mass ps C = mass ps c_true); nra. }
    apply psatisfies_and; split; [exact HS|].
    apply psatisfies_and; split; apply psatisfies_eq; [exact HTotal|].
    change (mass ps (FProgBool out) = delivery initial true * pstate_prob_logic_values ps y).
    rewrite <- HT. apply (mass_on_support ps C _ _ Hps HS).
    intros w Hw; rewrite satisfies_and; cbn [bit]; tauto.
Qed.

End Relay.

Section RelayLaws.
Context {D : Domain}.
Variables (out coin input : BoolProgramVar) (p d : R).
Hypotheses (out_coin : out <> coin) (out_go : out <> go) (coin_go : coin <> go)
  (input_out : input <> out) (input_coin : input <> coin) (input_go : input <> go).
Hypotheses (Hp : 0 < p < 1) (Hd : 0 < d <= 1).

Definition stable (C : CFormula D) :=
  (forall w z, satisfies (update_bool w out z) C <-> satisfies w C) /\
  (forall w z, satisfies (update_bool w coin z) C <-> satisfies w C) /\
  (forall w z, satisfies (update_bool w go z) C <-> satisfies w C).

Lemma stable_not C : stable C -> stable (c_not C).
Proof.
  intros [H1 [H2 H3]]; unfold stable; split; [|split]; intros w z;
    cbn [c_not satisfies];
    rewrite ?H1, ?H2, ?H3; tauto.
Qed.

Lemma stable_input_class C i : stable C -> stable (c_and C (bit input i)).
Proof.
  intros [H1 [H2 H3]]. unfold stable; split; [|split]; intros w z;
    rewrite !satisfies_and, !satisfies_bit;
    rewrite ?H1, ?H2, ?H3, bool_update_other by congruence; reflexivity.
Qed.

Definition signed (C : CFormula D) (present : bool) := if present then C else c_not C.
Definition relay_event (C : CFormula D) (with_output : bool) :=
  if with_output then c_and C (FProgBool out) else C.
Definition class_weight (present with_output initial : bool) :=
  if present then (if with_output then delivery p d initial true else 1) else 0.
Definition relay_input_term (C : CFormula D) (present with_output : bool) : Pterm D :=
  PAdd
    (condition_pterm (PMul (PConst (class_weight present with_output true)) (PProb c_true))
      (c_and (signed C present) (bit input true)))
    (condition_pterm (PMul (PConst (class_weight present with_output false)) (PProb c_true))
      (c_and (signed C present) (bit input false))).
Definition channel_term (C : CFormula D) (with_output : bool) : Pterm D :=
  if with_output then
    PAdd (PMul (PConst (flip_probability p d)) (PProb C))
      (PMul (PConst (1-2*flip_probability p d)) (PProb (c_and C (FProgBool input))))
  else PProb C.

Lemma relay_leaf C present with_output initial y : stable C ->
  hoare_derivable
    (p_and (p_eq (PVar y)
      (PMul (PConst (class_weight present with_output initial)) (PProb c_true)))
      (p_almost_sure (c_and (signed C present) (bit input initial))))
    (relay out coin p d input)
    (p_eq (PVar y) (PProb (relay_event C with_output))).
Proof.
  intro HC. apply scaled_transfer; intro m.
  assert (HS : stable (signed C present)).
  { destruct present; cbn [signed]; [exact HC|apply stable_not; exact HC]. }
  destruct (stable_input_class _ initial HS) as [H1 [H2 H3]].
  eapply derive_post.
  - apply (relay_class_summary out coin p d out_coin out_go
      (c_and (signed C present) (bit input initial)) H1 H2 H3 input initial m);
      try assumption.
    intros w Hw; apply satisfies_and in Hw; apply satisfies_bit; tauto.
  - intros ps Hps H; apply psatisfies_and in H; destruct H as [HS' H].
    apply psatisfies_and in H; destruct H as [HM HO].
    apply psatisfies_eq in HM, HO. apply psatisfies_eq.
    change (mass ps (relay_event C with_output) =
      class_weight present with_output initial * pstate_prob_logic_values ps m).
    destruct present, with_output; cbn [relay_event class_weight].
    + rewrite (mass_on_support ps (c_and (signed C true) (bit input initial))
        _ (FProgBool out) Hps HS'); [exact HO|].
      intros w Hw; cbn [signed] in Hw; rewrite satisfies_and in Hw |- *; tauto.
    + rewrite (mass_on_support ps (c_and (signed C true) (bit input initial))
        C c_true Hps HS'); [change (mass ps c_true = pstate_prob_logic_values ps m) in HM; lra|].
      intros w Hw; cbn [signed] in Hw; rewrite satisfies_and in Hw; cbn; tauto.
    + rewrite (mass_on_support ps (c_and (signed C false) (bit input initial))
        _ FFalse Hps HS'); [rewrite mass_false; ring|].
      intros w Hw; cbn [signed] in Hw; rewrite satisfies_and in Hw |- *; cbn in *; tauto.
    + rewrite (mass_on_support ps (c_and (signed C false) (bit input initial))
        C FFalse Hps HS'); [rewrite mass_false; ring|].
      intros w Hw; cbn [signed] in Hw; rewrite satisfies_and in Hw; cbn in *; tauto.
Qed.

Lemma relay_input_transfer C present with_output y : stable C ->
  hoare_derivable
    (p_and (p_eq (PVar y) (relay_input_term C present with_output))
      (p_almost_sure (signed C present)))
    (relay out coin p d input)
    (p_eq (PVar y) (PProb (relay_event C with_output))).
Proof.
  intro HC. eapply derive_pre; [|apply (split_transfer
    (relay out coin p d input)
    (c_and (signed C present) (bit input true))
    (c_and (signed C present) (bit input false)) (relay_event C with_output)
    (PMul (PConst (class_weight present with_output true)) (PProb c_true))
    (PMul (PConst (class_weight present with_output false)) (PProb c_true)));
    [intros; cbn; tauto|intros; cbn; tauto| |intro; apply relay_leaf; exact HC|
      intro; apply relay_leaf; exact HC]].
  - intros ps Hps H; apply psatisfies_and in H; destruct H as [HE HS].
    apply psatisfies_and; split; [exact HE|].
    apply psatisfies_almost_sure.
    apply (mass_on_support ps (signed C present) _ c_true Hps HS).
    intros w Hw; rewrite satisfies_or, !satisfies_and, !satisfies_bit.
    destruct (bool_program_values w input); cbn; tauto.
  - intros w H; rewrite !satisfies_and, !satisfies_bit in H; intuition congruence.
Qed.

Lemma channel_term_eval C with_output ps : pstate_admissible ps ->
  pterm_eval
    (PAdd (condition_pterm (relay_input_term C true with_output) C)
      (condition_pterm (relay_input_term C false with_output) (c_not C))) ps =
  pterm_eval (channel_term C with_output) ps.
Proof.
  intro Hps.
  assert (E : forall i, mass ps (c_and C (c_and (c_and C (bit input i)) c_true)) =
    mass ps (c_and C (bit input i))).
  { intro i; apply mass_ext; intro w; rewrite !satisfies_and; cbn; tauto. }
  pose proof (mass_bit_pair ps C input true Hps) as HP.
  cbn [negb bit] in HP.
  unfold mass in E, HP; cbn [pterm_eval] in E, HP.
  destruct with_output; unfold relay_input_term, channel_term, class_weight, signed;
    cbn [condition_pterm pterm_eval delivery Bool.eqb]; fold (@mass D ps);
    rewrite (E true), (E false); cbn [bit]; nra.
Qed.

Lemma relay_event_transfer C with_output y : stable C ->
  hoare_derivable (p_eq (PVar y) (channel_term C with_output))
    (relay out coin p d input)
    (p_eq (PVar y) (PProb (relay_event C with_output))).
Proof.
  intro HC.
  eapply derive_pre with (pre' := p_and
    (p_eq (PVar y) (PAdd (condition_pterm (relay_input_term C true with_output) C)
      (condition_pterm (relay_input_term C false with_output) (c_not C))))
    (p_almost_sure (c_or C (c_not C)))).
  - intros ps Hps H; apply psatisfies_and; split.
    + apply psatisfies_eq in H; apply psatisfies_eq.
      cbn [pterm_eval] in H; rewrite channel_term_eval by exact Hps; exact H.
    + apply psatisfies_almost_sure; apply measure_extensional; intro w.
      unfold formula_assertion; rewrite satisfies_or; cbn; tauto.
  - apply split_transfer.
    + intro z; unfold relay_input_term; cbn; tauto.
    + intro z; unfold relay_input_term; cbn; tauto.
    + intros w H; apply satisfies_and in H; cbn in H; tauto.
    + intro z; exact (relay_input_transfer C true with_output z HC).
    + intro z; exact (relay_input_transfer C false with_output z HC).
Qed.

Lemma relay_moment C with_output target t precondition : stable C ->
  pterm_analytical t ->
  (forall w, satisfies w target <-> satisfies w (relay_event C with_output)) ->
  (forall ps, pstate_admissible ps -> psatisfies ps precondition ->
    pterm_eval (channel_term C with_output) ps = pterm_eval t ps) ->
  hoare_derivable precondition (relay out coin p d input) (p_eq (PProb target) t).
Proof.
  intros HC Ht HE Hpre.
  eapply derive_post.
  - eapply derive_pre with (pre' := p_eq (channel_term C with_output) t).
    + intros ps Hps H; apply psatisfies_eq; apply Hpre; assumption.
    + apply transfer_analytical; [intro; destruct with_output; cbn; tauto|exact Ht|].
      intro y; apply relay_event_transfer; exact HC.
  - intros ps Hps H; apply psatisfies_eq in H; apply psatisfies_eq.
    change (mass ps target = pterm_eval t ps).
    rewrite (mass_ext ps target (relay_event C with_output) HE); exact H.
Qed.

End RelayLaws.

Definition program {D : Domain} (p q d e : R) : Cmd D :=
  CSeq (CSeq (relay oa f p d a) (relay ob g q e b))
    (CBoolAssign alarm (c_and (FProgBool oa) (FProgBool ob))).

Definition input_class {D : Domain} : CFormula D := c_and (FProgBool a) (FProgBool b).
Section Fusion.
Context {D : Domain}.

Definition marginal (u : R) (y : ProbLogicVar) : Pterm D :=
  PAdd (PConst u) (PMul (PConst (1-2*u)) (PVar y)).
Definition pre : PFormula D :=
  p_and (p_eq (PProb c_true) (PConst 1))
    (p_and (p_eq (PProb (FProgBool a)) (PVar alpha))
      (p_and (p_eq (PProb (FProgBool b)) (PVar beta))
        (p_eq (PProb input_class)
          (PMul (PProb (FProgBool a)) (PProb (FProgBool b)))))).

Definition conditional_post : PFormula D :=
  p_eq
    (PMul (PProb (c_and (c_and input_class (FProgBool oa)) (FProgBool ob)))
      (PProb input_class))
    (PMul (PProb (c_and input_class (FProgBool oa)))
      (PProb (c_and input_class (FProgBool ob)))).

Definition post_with (alarm_event : CFormula D) p q d e : PFormula D :=
  p_and
    (p_eq (PProb (c_and (FProgBool oa) (FProgBool ob)))
      (PMul (PProb (FProgBool oa)) (PProb (FProgBool ob))))
    (p_and
      (p_eq (PProb (FProgBool oa)) (marginal (flip_probability p d) alpha))
      (p_and
        (p_eq (PProb (FProgBool ob)) (marginal (flip_probability q e) beta))
        (p_and
          (p_eq (PProb alarm_event)
            (PMul (marginal (flip_probability p d) alpha)
              (marginal (flip_probability q e) beta)))
          conditional_post))).

Definition post p q d e := post_with (FProgBool alarm) p q d e.

Lemma mass_and_comm (ps : Pstate D) A B :
  mass ps (c_and A B) = mass ps (c_and B A).
Proof. apply mass_ext; intro w; rewrite !satisfies_and; tauto. Qed.

Lemma mass_true_and (ps : Pstate D) A : mass ps (c_and c_true A) = mass ps A.
Proof. apply mass_ext; intro w; rewrite satisfies_and; cbn; tauto. Qed.

Lemma mass_absorb (ps : Pstate D) A B :
  (forall w, satisfies w A -> satisfies w B) -> mass ps (c_and A B) = mass ps A.
Proof. intro H; apply mass_ext; intro w; rewrite satisfies_and; split; [tauto|intro HA; auto]. Qed.

Ltac stable_formula :=
  unfold stable; split; [|split]; intros w z;
  repeat rewrite satisfies_and;
  cbn [satisfies update_bool a b oa ob go f g input_class]; tauto.

Lemma pre_eval ps : psatisfies ps pre <->
  mass ps c_true = 1 /\
  mass ps (FProgBool a) = pstate_prob_logic_values ps alpha /\
  mass ps (FProgBool b) = pstate_prob_logic_values ps beta /\
  mass ps input_class = mass ps (FProgBool a)*mass ps (FProgBool b).
Proof. unfold pre; rewrite !psatisfies_and, !psatisfies_eq; reflexivity. Qed.

Lemma post_eval ps alarm_event p q d e : psatisfies ps (post_with alarm_event p q d e) <->
  mass ps (c_and (FProgBool oa) (FProgBool ob)) = mass ps (FProgBool oa)*mass ps (FProgBool ob) /\
  mass ps (FProgBool oa) = flip_probability p d +
    (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha /\
  mass ps (FProgBool ob) = flip_probability q e +
    (1-2*flip_probability q e)*pstate_prob_logic_values ps beta /\
  mass ps alarm_event =
    (flip_probability p d + (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha)*
    (flip_probability q e + (1-2*flip_probability q e)*pstate_prob_logic_values ps beta) /\
  mass ps (c_and (c_and input_class (FProgBool oa)) (FProgBool ob))*mass ps input_class =
    mass ps (c_and input_class (FProgBool oa))*mass ps (c_and input_class (FProgBool ob)).
Proof. unfold post_with, conditional_post; rewrite !psatisfies_and, !psatisfies_eq; reflexivity. Qed.


Definition joint_input : Pterm D := PMul (PVar alpha) (PVar beta).

(** The interface between the two relays records just the probabilities
    needed by the client.  Every right-hand side is an analytical term. *)
Definition after_a p d : PFormula D := pformula_conjunction
  [p_eq (PProb c_true) (PConst 1);
   p_eq (PProb (FProgBool b)) (PVar beta);
   p_eq (PProb input_class) joint_input;
   p_eq (PProb (FProgBool oa)) (marginal (flip_probability p d) alpha);
   p_eq (PProb (c_and (FProgBool b) (FProgBool oa)))
     (PMul (PVar beta) (marginal (flip_probability p d) alpha));
   p_eq (PProb (c_and input_class (FProgBool oa)))
     (PMul (PConst (1-flip_probability p d)) joint_input)].

Lemma after_a_eval ps p d : psatisfies ps (after_a p d) <->
  mass ps c_true = 1 /\
  mass ps (FProgBool b) = pstate_prob_logic_values ps beta /\
  mass ps input_class = pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta /\
  mass ps (FProgBool oa) = flip_probability p d +
    (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha /\
  mass ps (c_and (FProgBool b) (FProgBool oa)) = pstate_prob_logic_values ps beta*
    (flip_probability p d + (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha) /\
  mass ps (c_and input_class (FProgBool oa)) = (1-flip_probability p d)*
    (pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta).
Proof.
  unfold after_a; cbn [pformula_conjunction].
  rewrite !psatisfies_and, !psatisfies_eq.
  pose proof (psatisfies_true ps).
  unfold marginal, joint_input, mass; cbn [pterm_eval]; tauto.
Qed.

Ltac moment stable_event includes_output :=
  eapply relay_moment with (C := stable_event) (with_output := includes_output);
    try discriminate; try assumption;
    [stable_formula
    |cbn [marginal joint_input pterm_analytical]; tauto
    |intro w; cbn [relay_event]; repeat rewrite satisfies_and; cbn; tauto
    |].

Ltac eval_channel :=
  unfold channel_term, marginal, joint_input;
  cbn [pterm_eval];
  repeat match goal with
  | |- context [measure_of (pstate_measure ?ps) (formula_assertion ?event)] =>
      progress change (measure_of (pstate_measure ps) (formula_assertion event)) with (mass ps event)
  end.

Lemma relay_a_moments p d : 0 < p < 1 -> 0 < d <= 1 ->
  hoare_derivable pre (relay oa f p d a) (after_a p d).
Proof.
  intros Hp Hd. unfold after_a. apply derive_conjunction.
  intros eta Heta; cbn in Heta.
  destruct Heta as [<-|[<-|[<-|[<-|[<-|[<-|Heta]]]]]]; try contradiction.
  - moment (@c_true D) false.
    intros ps Hps H; apply pre_eval in H; eval_channel; tauto.
  - moment (@FProgBool D b) false.
    intros ps Hps H; apply pre_eval in H; eval_channel; tauto.
  - moment (@input_class D) false.
    intros ps Hps H; apply pre_eval in H; destruct H as [Hm [Ha [Hb HC]]].
    eval_channel; rewrite HC, Ha, Hb; reflexivity.
  - moment (@c_true D) true.
    intros ps Hps H; apply pre_eval in H; destruct H as [Hm [Ha [Hb HC]]].
    eval_channel; rewrite mass_true_and, Hm, Ha; ring.
  - moment (@FProgBool D b) true.
    intros ps Hps H; apply pre_eval in H; destruct H as [Hm [Ha [Hb HC]]].
    eval_channel; rewrite (mass_and_comm ps (FProgBool b) (FProgBool a)).
    fold (@input_class D); rewrite HC, Ha, Hb; ring.
  - moment (@input_class D) true.
    intros ps Hps H; apply pre_eval in H; destruct H as [Hm [Ha [Hb HC]]].
    eval_channel; rewrite (mass_absorb ps input_class (FProgBool a)).
    + rewrite HC, Ha, Hb; ring.
    + intros w Hw; unfold input_class in Hw; apply satisfies_and in Hw; tauto.
Qed.

Definition after_b p q d e : PFormula D := pformula_conjunction
  [p_eq (PProb (FProgBool oa)) (marginal (flip_probability p d) alpha);
   p_eq (PProb (FProgBool ob)) (marginal (flip_probability q e) beta);
   p_eq (PProb (c_and (FProgBool oa) (FProgBool ob)))
     (PMul (marginal (flip_probability p d) alpha) (marginal (flip_probability q e) beta));
   p_eq (PProb input_class) joint_input;
   p_eq (PProb (c_and input_class (FProgBool oa)))
     (PMul (PConst (1-flip_probability p d)) joint_input);
   p_eq (PProb (c_and input_class (FProgBool ob)))
     (PMul (PConst (1-flip_probability q e)) joint_input);
   p_eq (PProb (c_and (c_and input_class (FProgBool oa)) (FProgBool ob)))
     (PMul (PConst ((1-flip_probability q e)*(1-flip_probability p d))) joint_input)].

Lemma after_b_eval ps p q d e : psatisfies ps (after_b p q d e) <->
  mass ps (FProgBool oa) = flip_probability p d +
    (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha /\
  mass ps (FProgBool ob) = flip_probability q e +
    (1-2*flip_probability q e)*pstate_prob_logic_values ps beta /\
  mass ps (c_and (FProgBool oa) (FProgBool ob)) =
    (flip_probability p d + (1-2*flip_probability p d)*pstate_prob_logic_values ps alpha)*
    (flip_probability q e + (1-2*flip_probability q e)*pstate_prob_logic_values ps beta) /\
  mass ps input_class = pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta /\
  mass ps (c_and input_class (FProgBool oa)) = (1-flip_probability p d)*
    (pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta) /\
  mass ps (c_and input_class (FProgBool ob)) = (1-flip_probability q e)*
    (pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta) /\
  mass ps (c_and (c_and input_class (FProgBool oa)) (FProgBool ob)) =
    (1-flip_probability q e)*(1-flip_probability p d)*
      (pstate_prob_logic_values ps alpha*pstate_prob_logic_values ps beta).
Proof.
  unfold after_b; cbn [pformula_conjunction].
  rewrite !psatisfies_and, !psatisfies_eq.
  pose proof (psatisfies_true ps).
  unfold marginal, joint_input, mass; cbn [pterm_eval]; tauto.
Qed.

Lemma relay_b_moments p q d e : 0 < q < 1 -> 0 < e <= 1 ->
  hoare_derivable (after_a p d) (relay ob g q e b) (after_b p q d e).
Proof.
  intros Hq He. unfold after_b. apply derive_conjunction.
  intros eta Heta; cbn in Heta.
  destruct Heta as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Heta]]]]]]]; try contradiction.
  - moment (@FProgBool D oa) false.
    intros ps Hps H; apply after_a_eval in H; eval_channel; tauto.
  - moment (@c_true D) true.
    intros ps Hps H; apply after_a_eval in H; destruct H as [Hm [Hb [HC [Ha [Hba HCa]]]]].
    eval_channel; rewrite mass_true_and, Hm, Hb; ring.
  - moment (@FProgBool D oa) true.
    intros ps Hps H; apply after_a_eval in H; destruct H as [Hm [Hb [HC [Ha [Hba HCa]]]]].
    eval_channel; rewrite (mass_and_comm ps (FProgBool oa) (FProgBool b)), Ha, Hba; ring.
  - moment (@input_class D) false.
    intros ps Hps H; apply after_a_eval in H; eval_channel; tauto.
  - moment (@c_and D input_class (FProgBool oa)) false.
    intros ps Hps H; apply after_a_eval in H; eval_channel; tauto.
  - moment (@input_class D) true.
    intros ps Hps H; apply after_a_eval in H; destruct H as [Hm [Hb [HC [Ha [Hba HCa]]]]].
    eval_channel; rewrite (mass_absorb ps input_class (FProgBool b)).
    + rewrite HC; ring.
    + intros w Hw; unfold input_class in Hw; apply satisfies_and in Hw; tauto.
  - moment (@c_and D input_class (FProgBool oa)) true.
    intros ps Hps H; apply after_a_eval in H; destruct H as [Hm [Hb [HC [Ha [Hba HCa]]]]].
    eval_channel; rewrite (mass_absorb ps (c_and input_class (FProgBool oa)) (FProgBool b)).
    + rewrite HCa; ring.
    + intros w Hw; unfold input_class in Hw; rewrite !satisfies_and in Hw; tauto.
Qed.

Lemma relays_derivable p q d e :
  0 < p < 1 -> 0 < q < 1 -> 0 < d <= 1 -> 0 < e <= 1 ->
  hoare_derivable pre (CSeq (relay oa f p d a) (relay ob g q e b))
    (post_with (c_and (FProgBool oa) (FProgBool ob)) p q d e).
Proof.
  intros Hp Hq Hd He. eapply derive_post with (post := after_b p q d e).
  - eapply HSeq; [apply relay_a_moments|apply relay_b_moments]; assumption.
  - intros ps Hps H; apply after_b_eval in H.
    destruct H as [Ha [Hb [Hab [HC [HCa [HCb HCab]]]]]].
    apply post_eval; rewrite Ha, Hb, Hab, HC, HCa, HCb, HCab.
    repeat split; ring.
Qed.

(** A direct derivation: SEQ composes the relay interfaces, CONS establishes
    the polynomial relations, and ASGB performs the final fusion. *)
Theorem sensor_fusion p q d e :
  0 < p < 1 -> 0 < q < 1 -> 0 < d <= 1 -> 0 < e <= 1 ->
  hoare_derivable pre (program p q d e) (post p q d e).
Proof.
  intros Hp Hq Hd He. unfold program.
  eapply HSeq with (eta2 := post_with (c_and (FProgBool oa) (FProgBool ob)) p q d e).
  - apply relays_derivable; assumption.
  - change (hoare_derivable
      (subst_bool_pformula alarm (c_and (FProgBool oa) (FProgBool ob)) (post p q d e))
      (CBoolAssign alarm (c_and (FProgBool oa) (FProgBool ob))) (post p q d e)).
    apply HBoolAssign.
Qed.

End Fusion.

End SensorFusion.
