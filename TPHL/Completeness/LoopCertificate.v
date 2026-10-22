(** The certificate for [while beta do body] (App. D, Lemma 25, while case):
      T(gamma) = sum_a x_a * Pr(gamma_a)
    over the classes [a] of the variables of the loop and of [gamma].  The
    per-class triples of LoopRules.v are stitched together with [SUM]
    (as the derived rule SUMS of App. C, Lemma 23) and [ELIMV]. *)
From Stdlib Require Import Reals List Lra Lia.
From mathcomp Require boolp.
Require Import MeasureIntegration PHL.
Require Import Soundness.StateFacts Soundness.AssertionFacts Soundness.TransformerAssertions
  Soundness.SplitRules.
Require Import Completeness.Interface Completeness.Freshness Completeness.StructuralRules
  Completeness.WeakestPrecondition Completeness.FiniteDomain Completeness.LoopClasses
  Completeness.LoopRules.
Import ListNotations.

Local Open Scope R_scope.

Section LoopCertificate.
Context {D : Domain} (FD : FiniteDomain D).
Variables (beta gamma : CFormula D) (body : Cmd D).
Hypothesis body_complete :
  forall pre post, hoare_valid pre body post -> hoare_derivable pre body post.

Local Notation W := (loop_cmd beta body).
Local Notation V := (loop_vars beta gamma body).
Local Notation cls := (cls FD beta gamma body).
Local Notation xv := (xv FD beta gamma body).
Local Notation Gf a := (class_formula FD a).
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).
Local Notation post y := (p_eq (PVar y) (PProb gamma) : PFormula).

Definition term (a : @Assignment D) : Pterm := PMul (PConst (xv a)) (PProb (Gf a)).

Fixpoint psum (l : list (@Assignment D)) : Pterm :=
  match l with
  | [] => PConst 0
  | a :: l' => PAdd (term a) (psum l')
  end.

Fixpoint big_or (l : list (@Assignment D)) : CFormula D :=
  match l with
  | [] => FFalse
  | a :: l' => c_or (Gf a) (big_or l')
  end.

Definition Q (l : list (@Assignment D)) (y : ProbLogicVar) : PFormula :=
  p_and (p_almost_sure (big_or l)) (p_eq (PVar y) (psum l)).

Lemma psum_no_vars l y : ~ prob_logic_var_occurs_pterm y (psum l).
Proof. induction l; cbn; tauto. Qed.

Lemma satisfies_big_or w l : satisfies w (big_or l) <-> exists a, In a l /\ satisfies w (Gf a).
Proof.
  induction l as [|a l IH]; cbn [big_or].
  - split; [contradiction | intros [a [[] _]]].
  - rewrite satisfies_or, IH. split.
    + intros [h | [b [hb h]]]; [exists a; split; [left|]; auto | exists b; split; [right|]; auto].
    + intros [b [[<-|hb] h]]; [left; exact h | right; exists b; auto].
Qed.

Lemma psum_restrict l ps S :
  (forall a w, In a l -> satisfies w (Gf a) -> satisfies w S) ->
  pterm_eval (psum l) (pstate_restrict ps S) = pterm_eval (psum l) ps.
Proof.
  induction l as [|a l IH]; intros H; cbn [psum pterm_eval]; [reflexivity|].
  rewrite IH by (intros; apply (H a0 w); [right|]; assumption).
  unfold term; cbn [pterm_eval]. rewrite restrict_measure_of.
  f_equal. f_equal. apply measure_extensional. intros v. unfold formula_assertion.
  split; [tauto | intros hv; split; [exact hv | apply (H a v); [left; reflexivity | exact hv]]].
Qed.

Lemma classes_disjoint_cls a b w : In a cls -> In b cls ->
  satisfies w (Gf a) -> satisfies w (Gf b) -> a = b.
Proof. intros ha hb. exact (classes_disjoint FD V a b w ha hb). Qed.

(** One class, with the target value bound to [y]. *)
Lemma single a y : In a cls ->
  hoare_derivable (p_and (p_eq (PVar y) (term a)) (p_almost_sure (Gf a))) W (post y).
Proof.
  intros ha.
  set (y' := fresh_prob_logic_var [y]).
  assert (Hy' : ~ In y' [y]) by apply fresh_prob_logic_var_not_in.
  assert (hne : y <> y') by (intros e; apply Hy'; left; exact e).
  set (F := p_eq (PVar y) (PMul (PConst (xv a)) (PVar y')) : PFormula).
  assert (HF : pformula_analytical F) by (cbn; tauto).
  pose proof (derive_analytical_frame _ _ _ _ HF (per_class FD beta gamma body body_complete a y' ha)) as H1.
  assert (H3 : hoare_derivable (p_and (p_and (p_almost_sure (Gf a)) F)
                  (p_eq (PVar y') (PProb c_true))) W (post y)).
  { eapply derive_post; [eapply derive_pre; [| exact H1] |].
    - intros ps _ H. rewrite !psatisfies_and in H |- *. destruct H as [[HG HFp] Hy].
      split; [split; [exact HG|] | exact HFp].
      apply psatisfies_eq in Hy. apply psatisfies_eq. cbn in *. lra.
    - intros ps _ H. rewrite !psatisfies_and in H. destruct H as [Hg HFp].
      apply psatisfies_eq in Hg, HFp. apply psatisfies_eq. cbn in *. lra. }
  assert (Hpost : ~ prob_logic_var_occurs_pformula y' (post y)) by (cbn; intuition congruence).
  pose proof (HElimv _ _ y' (PProb c_true) W H3 ltac:(cbn; tauto) Hpost) as H4.
  eapply derive_pre; [| exact H4].
  intros ps _ H. apply subst_prob_pformula_correct.
  rewrite psatisfies_and in H |- *. destruct H as [Hy HG].
  split.
  - apply (psatisfies_update_fresh y' _ _ ps); [cbn; tauto | exact HG].
  - apply psatisfies_almost_sure in HG. apply psatisfies_eq in Hy. apply psatisfies_eq.
    cbn [pterm_eval pstate_update_prob pstate_prob_logic_values pstate_measure term] in *.
    rewrite update_prob_here, update_prob_other by exact hne.
    rewrite Hy. rewrite HG. reflexivity.
Qed.

(** Adding one class to the front of a list of classes. *)
Lemma sum_step a l : In a cls -> ~ In a l -> incl l cls ->
  (forall y, hoare_derivable (Q l y) W (post y)) ->
  forall y, hoare_derivable (Q (a :: l) y) W (post y).
Proof.
  intros ha hal hl IH y.
  set (y1 := fresh_prob_logic_var [y]).
  set (y2 := fresh_prob_logic_var [y1; y]).
  assert (H1n : ~ In y1 [y]) by apply fresh_prob_logic_var_not_in.
  assert (H2n : ~ In y2 [y1; y]) by apply fresh_prob_logic_var_not_in.
  cbn in H1n, H2n.
  assert (hy1 : y <> y1) by tauto. assert (hy2 : y <> y2) by tauto.
  assert (h12 : y1 <> y2) by tauto.
  set (S := big_or l).
  assert (hdis : cformula_valid (c_not (c_and (Gf a) S))).
  { intros w hw. apply satisfies_and in hw. destruct hw as [hwa hwS].
    apply satisfies_big_or in hwS. destruct hwS as [b [hb hwb]].
    apply hal. rewrite (classes_disjoint_cls a b w ha (hl b hb) hwa hwb). exact hb. }
  assert (H2 : hoare_derivable (p_and (Q l y2) (p_almost_sure S)) W (post y2)).
  { eapply derive_pre; [| exact (IH y2)]. intros ps _ H; apply psatisfies_and in H; tauto. }
  pose proof (derive_sum_eq _ _ (Gf a) S gamma y1 y2 W hdis (single a y1 ha) H2) as HS.
  set (F := p_eq (PVar y) (PAdd (PVar y1) (PVar y2)) : PFormula).
  assert (HFa : pformula_analytical F) by (cbn; tauto).
  pose proof (derive_analytical_frame _ _ _ _ HFa HS) as HSF.
  set (frame := p_and (p_almost_sure (big_or (a :: l))) F).
  set (bs := [(y1, term a); (y2, psum l)]).
  assert (HB : hoare_derivable (bindings_precondition bs frame) W (post y)).
  { eapply derive_post; [eapply derive_pre; [| exact HSF] |].
    - intros ps hps H. cbn [bs bindings_precondition] in H. unfold frame in H.
      rewrite !psatisfies_and in H. destruct H as [[[HS' HFp] Hb2] Hb1].
      rewrite !psatisfies_and. split; [|exact HFp].
      unfold sum_precondition. rewrite !psatisfies_and.
      split; [split | exact HS'].
      + apply condition_pformula_correct.
        apply psatisfies_eq in Hb1. apply psatisfies_eq.
        unfold term in *; cbn [pterm_eval] in *. rewrite restrict_measure_of.
        change (pstate_prob_logic_values (pstate_restrict ps (Gf a)) y1)
          with (pstate_prob_logic_values ps y1).
        rewrite Hb1. f_equal. apply measure_extensional. intros v; unfold formula_assertion; tauto.
      + apply condition_pformula_correct. unfold Q. rewrite psatisfies_and. split.
        * apply psatisfies_almost_sure. rewrite !restrict_measure_of.
          apply measure_extensional. intros v; unfold formula_assertion.
          split; [intros [h _]; split; [apply satisfies_true | exact h] | tauto].
        * apply psatisfies_eq in Hb2. apply psatisfies_eq. cbn [pterm_eval] in *.
          change (pstate_prob_logic_values (pstate_restrict ps S) y2)
            with (pstate_prob_logic_values ps y2).
          rewrite psum_restrict; [exact Hb2|].
          intros b w hb hw. apply satisfies_big_or. exists b. split; assumption.
    - intros ps _ H. rewrite psatisfies_and in H. destruct H as [Hs HFp].
      apply psatisfies_eq in Hs, HFp. apply psatisfies_eq. cbn in *. lra. }
  assert (Hind : independent_bindings bs).
  { split.
    - cbn. constructor; [cbn; intros [e|[]]; congruence | constructor; [cbn; tauto | constructor]].
    - intros z p w r _ Hw. cbn in Hw. destruct Hw as [e|[e|[]]]; inversion e; subst.
      + unfold term; cbn; tauto.
      + apply psum_no_vars. }
  assert (Hpost : forall z p, In (z, p) bs -> ~ prob_logic_var_occurs_pformula z (post y)).
  { intros z p Hz. cbn in Hz. destruct Hz as [e|[e|[]]]; inversion e; subst;
      cbn; intuition congruence. }
  pose proof (derive_eliminate_bindings bs frame W (post y) Hind Hpost HB) as HE.
  eapply derive_pre; [| exact HE].
  intros ps _ H. apply substitute_bindings_correct.
  cbn [bs instantiate_bindings].
  unfold Q in H. rewrite psatisfies_and in H. destruct H as [HS' Hy].
  unfold frame. rewrite psatisfies_and. split.
  - apply (psatisfies_update_fresh y1); [cbn; tauto|].
    apply (psatisfies_update_fresh y2); [cbn; tauto|]. exact HS'.
  - apply psatisfies_eq in Hy. apply psatisfies_eq.
    cbn [pterm_eval pstate_update_prob pstate_prob_logic_values pstate_measure psum] in *.
    rewrite (update_prob_other _ y1 _ y hy1), (update_prob_other _ y2 _ y hy2).
    rewrite (update_prob_here _ y1).
    rewrite (update_prob_other _ y1 _ y2 (not_eq_sym h12)), (update_prob_here _ y2).
    rewrite (pterm_eval_update_fresh y2 _ (term a)) by (unfold term; cbn; tauto).
    exact Hy.
Qed.

Lemma assemble l : l <> [] -> incl l cls -> NoDup l ->
  forall y, hoare_derivable (Q l y) W (post y).
Proof.
  induction l as [|a l IH]; intros hne hl hnd; [contradiction|].
  inversion hnd as [|? ? hal hnd']; subst.
  assert (ha : In a cls) by (apply hl; left; reflexivity).
  assert (hl' : incl l cls) by (intros b hb; apply hl; right; exact hb).
  destruct l as [|b l'].
  - intros y. eapply derive_pre; [| exact (single a y ha)].
    intros ps _ H. unfold Q in H. rewrite psatisfies_and in H |- *. destruct H as [HS Hy].
    split.
    + apply psatisfies_eq in Hy. apply psatisfies_eq. unfold term; cbn [psum pterm_eval] in *.
      unfold term in Hy; cbn [pterm_eval] in Hy. lra.
    + apply psatisfies_almost_sure in HS. apply psatisfies_almost_sure.
      rewrite <- HS. apply measure_extensional. intros v; unfold formula_assertion; cbn [big_or].
      rewrite satisfies_or. cbn. tauto.
  - apply sum_step; [exact ha | exact hal | exact hl' |].
    apply IH; [discriminate | exact hl' | exact hnd'].
Qed.

(** The certificate. *)
Definition loop_term : Pterm := psum cls.

Lemma big_or_cls_valid w : satisfies w (big_or cls).
Proof. apply satisfies_big_or. exists (assignment_of V w). split; [apply classes_own | apply satisfies_own_class]. Qed.

Lemma loop_term_derivable y :
  hoare_derivable (p_eq (PVar y) loop_term) W (post y).
Proof.
  eapply derive_pre; [| exact (assemble cls (classes_nonnil FD V) (incl_refl _) (classes_nodup FD V) y)].
  intros ps _ H. unfold Q. rewrite psatisfies_and. split; [|exact H].
  apply psatisfies_almost_sure. apply measure_extensional. intros v; unfold formula_assertion.
  split; [intros _; apply satisfies_true | intros _; apply big_or_cls_valid].
Qed.

Lemma psum_eval l ps :
  pterm_eval (psum l) ps = rsum l (fun a => xv a * measure_of (pstate_measure ps) (G FD a)).
Proof. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma loop_term_correct ps : pstate_admissible ps ->
  pterm_eval loop_term ps = pterm_eval (PProb gamma) (CommandSemantics.run W ps).
Proof.
  intros hps. unfold loop_term. rewrite psum_eval. cbn [pterm_eval].
  symmetry. exact (@loop_output_mass D FD beta gamma body ps hps).
Qed.

End LoopCertificate.

Definition loop_transformer {D : Domain} (FD : FiniteDomain D) (beta : CFormula D)
    (body : Cmd D) (gamma : CFormula D) : Pterm D :=
  loop_term FD beta gamma body.

Theorem loop_certificate {D : Domain} (FD : FiniteDomain D) (beta : CFormula D) (body : Cmd D) :
  (forall pre post, hoare_valid pre body post -> hoare_derivable pre body post) ->
  certificate (CWhile beta body) (loop_transformer FD beta body).
Proof.
  intros Hbody. constructor.
  - intros gamma y. apply psum_no_vars.
  - intros ps gamma hps. exact (loop_term_correct FD beta gamma body ps hps).
  - intros gamma y. exact (loop_term_derivable FD beta gamma body Hbody y).
Qed.
