(** A bounded-retry batch protocol over the unbounded natural-number domain.
    K counts total attempts, not retransmissions after an initial attempt.
    The fast-path probability rho^N requires K > 0.
*)
From Stdlib Require Import Reals Lra Psatz Lia List Bool String FunctionalExtensionality Arith.Compare_dec.
Require Import MeasureIntegration PHL Soundness.StateFacts Soundness.AssertionFacts
  Soundness.SplitRules Completeness.StructuralRules
  Completeness.Interface Completeness.AtomicCertificates Completeness.CompositeCertificates
  Completeness.WeakestPreterm Completeness.WeakestPrecondition.
Import ListNotations.
Open Scope R_scope.
Open Scope string_scope.

Module BatchTransfer.

(** * General probability and loop helpers *)
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

Section LoopFree.
Context {D : Domain}.

Fixpoint loop_free (c : Cmd D) : Prop :=
  match c with
  | CWhile _ _ => False
  | CBoolToss _ r => coin_probability_valid r
  | CSeq c1 c2 | CIf _ c1 c2 => loop_free c1 /\ loop_free c2
  | _ => True
  end.

Fixpoint preterm (c : Cmd D) (target : CFormula D) : Pterm D :=
  match c with
  | CSkip => PProb target
  | CDomAssign x t => subst_dom_pterm x t (PProb target)
  | CBoolAssign x g => subst_bool_pterm x g (PProb target)
  | CBoolToss x r => toss_pterm x r (PProb target)
  | CSeq c1 c2 => lift_preterm (preterm c1) (preterm c2 target)
  | CIf g c1 c2 => PAdd (condition_pterm (preterm c1 target) g)
      (condition_pterm (preterm c2 target) (c_not g))
  | CWhile _ _ => PConst 0
  end.

Lemma loop_free_certificate c : loop_free c -> certificate c (preterm c).
Proof.
  induction c; cbn [loop_free]; intro H.
  - apply skip_certificate.
  - apply dom_assign_certificate.
  - apply bool_assign_certificate.
  - apply valid_toss_certificate; exact H.
  - destruct H as [H1 H2]. apply (seq_certificate c1 c2 (preterm c1) (preterm c2)); auto.
  - destruct H as [H1 H2]. apply (if_certificate beta c1 c2 (preterm c1) (preterm c2)); auto.
  - contradiction.
Qed.

Lemma loop_free_exact c pre target value : loop_free c ->
  (forall ps, pstate_admissible ps -> psatisfies ps pre ->
    pterm_eval (preterm c target) ps = value) ->
  hoare_derivable pre c (p_eq (PProb target) (PConst value)).
Proof.
  intros Hc H. eapply derive_pre;
    [|apply (wp_derivable c (preterm c) (loop_free_certificate c Hc))].
  intros ps Hps Hp. change (psatisfies ps (p_eq (preterm c target) (PConst value))).
  apply psatisfies_eq; cbn [pterm_eval]; apply H; assumption.
Qed.

Lemma derive_finite_and m (post : nat -> PFormula D) pre c :
  (forall i, (i < m)%nat -> hoare_derivable pre c (post i)) ->
  hoare_derivable pre c (finite_p_and m post).
Proof.
  induction m; intro H; cbn [finite_p_and].
  - apply derive_true.
  - apply HAnd; [apply IHm; intros; apply H; lia|apply H; lia].
Qed.

End LoopFree.

(** Instantiate a loop's mass parameter at one, retaining its analytical
    equality through the command. The remaining goal is the loop rule itself. *)
Ltac with_unit_mass pre cmd result bound y :=
  change (hoare_derivable (subst_prob_pformula y (PConst 1) pre) cmd result);
  eapply (HElimv pre result y (PConst 1) cmd); [|cbn; tauto|cbn; tauto];
  eapply derive_post with (post := p_and bound (p_eq (PVar y) (PConst 1)));
  [apply HAnd;
    [|eapply derive_pre; [|apply HFree; cbn; tauto];
      intros ps Hps H; apply psatisfies_and in H; tauto]
  |intros ps Hps H; rewrite !psatisfies_and, !psatisfies_eq in H;
    try apply psatisfies_eq; cbn in H |- *; intuition nra].

Section LoopCertificates.
Context {D : Domain}.

Lemma lower_unit m k (beta gamma : CFormula D) (body : Cmd D)
  (regions : nat -> CFormula D) solution exits transitions :
  (k < m)%nat ->
  while_regions_in_guard m beta regions ->
  while_regions_disjoint m regions -> while_progress m transitions exits ->
  (forall i, (i < m)%nat -> hoare_derivable (p_concentrated_unit (regions i)) body
    (while_body_post_lower m regions (transitions i) beta gamma (exits i))) ->
  while_lower_solution m solution transitions exits ->
  hoare_derivable (p_concentrated_unit (regions k)) (CWhile beta body)
    (PFLe (PConst (solution k)) (PProb gamma)).
Proof.
  intros Hk Hguard Hdis Hprogress Hbody Hsol.
  set (y := prob_logic_var "unit_mass").
  with_unit_mass (p_concentrated_unit (regions k)) (CWhile beta body)
    (PFLe (PConst (solution k)) (PProb gamma))
    (PFLe (PMul (PConst (solution k)) (PVar y)) (PProb gamma)) y.
  eapply derive_pre; [|exact (HWhileLower m k beta gamma body regions solution exits
    transitions y Hk Hguard Hdis Hprogress Hbody Hsol)].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [HU Hy].
  apply psatisfies_and in HU; destruct HU as [Hs Hm].
  apply psatisfies_eq in Hm, Hy. apply psatisfies_and; split.
  - apply psatisfies_almost_sure.
    apply (mass_on_support ps (regions k) _ c_true Hps Hs).
    intros w Hw; rewrite satisfies_and; split; [intros _; apply satisfies_true|].
    intros _; split; [exact (Hguard k Hk w Hw)|exact Hw].
  - cbn in Hm, Hy |- *; lra.
Qed.

Lemma unit_of_probability_one ps (A : CFormula D) : pstate_admissible ps ->
  psatisfies ps (p_eq (PProb A) (PConst 1)) -> psatisfies ps (p_concentrated_unit A).
Proof.
  intros Hps H; apply psatisfies_eq in H.
  pose proof (mass_true_le ps Hps).
  pose proof (mass_mono ps A c_true Hps (fun w _ => satisfies_true w)).
  change (mass ps A = 1) in H.
  apply psatisfies_and; split; [apply psatisfies_almost_sure|apply psatisfies_eq];
    change (mass ps A = mass ps c_true) || change (mass ps c_true = 1); lra.
Qed.

Lemma assign_unit x value (A B : CFormula D) :
  (forall w, satisfies w A -> satisfies (update_bool w x (cformula_eval_bool value w)) B) ->
  hoare_derivable (p_concentrated_unit A) (CBoolAssign x value) (p_concentrated_unit B).
Proof.
  intro H. eapply derive_pre; [|apply HBoolAssign].
  intros ps Hps Hpre; apply psatisfies_and in Hpre; destruct Hpre as [Hs Hm].
  change (psatisfies ps (p_concentrated_unit (subst_bool_cformula x value B))).
  apply psatisfies_and; split; [|exact Hm]. apply psatisfies_almost_sure.
  apply (mass_on_support ps A _ c_true Hps Hs).
  intros w Hw; rewrite subst_bool_cformula_correct; split;
    [intros _; apply satisfies_true|intros _; apply H; exact Hw].
Qed.

Lemma while_not_unit (A beta gamma : CFormula D) body :
  (forall w, satisfies w A -> ~ satisfies w beta /\ satisfies w gamma) ->
  hoare_derivable (p_concentrated_unit A) (CWhile beta body)
    (p_eq (PProb gamma) (PConst 1)).
Proof.
  intro HA. set (y := prob_logic_var "unit_mass").
  with_unit_mass (p_concentrated_unit A) (CWhile beta body)
    (p_eq (PProb gamma) (PConst 1))
    (p_and (p_eq (PProb gamma) (PProb c_true)) (p_eq (PProb c_true) (PVar y))) y.
  eapply derive_pre; [|apply HWhileNot].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [HU Hy].
  apply psatisfies_and in HU; destruct HU as [Hs Hm].
  apply psatisfies_eq in Hm, Hy. apply psatisfies_and; split.
  - apply psatisfies_almost_sure.
    apply (mass_on_support ps A _ c_true Hps Hs).
    intros w Hw; rewrite satisfies_and; specialize (HA w Hw); cbn; tauto.
  - apply psatisfies_eq; cbn in Hm, Hy |- *; lra.
Qed.

Lemma finite_delta m k (v : R) : (k < m)%nat ->
  finite_r_sum m (fun j => if Nat.eq_dec j k then v else 0) = v.
Proof.
  revert k; induction m; intros k Hk; [lia|]. cbn [finite_r_sum].
  destruct (Nat.eq_dec m k) as [->|Hne].
  - assert (E : finite_r_sum k (fun j => if Nat.eq_dec j k then v else 0) = 0).
    { clear Hk IHm. induction k; cbn [finite_r_sum]; [reflexivity|].
      assert (Z : forall n, (n <= k)%nat ->
        finite_r_sum n (fun j => if Nat.eq_dec j (S k) then v else 0) = 0).
      { induction n; intro Hn; cbn [finite_r_sum]; [reflexivity|].
        rewrite IHn by lia; destruct (Nat.eq_dec n (S k)); [lia|ring]. }
      rewrite Z by lia; destruct (Nat.eq_dec k (S k)); [lia|ring]. }
    rewrite E; ring.
  - rewrite IHm by lia; ring.
Qed.

Lemma weighted_delta m k rate (x : nat -> R) : (k < m)%nat ->
  finite_r_sum m (fun j => (if Nat.eq_dec j k then rate else 0)*x j) = rate*x k.
Proof.
  intro Hk. rewrite <- (finite_delta m k (rate*x k) Hk).
  f_equal; apply functional_extensionality; intro j.
  destruct (Nat.eq_dec j k); subst; ring.
Qed.

Definition chain_transition rate i j :=
  if Nat.eq_dec i 0 then 0 else if Nat.eq_dec j (i-1) then rate else 0.

Lemma chain_sum m i rate x : (i < m)%nat ->
  finite_r_sum m (fun j => chain_transition rate i j*x j) =
    if Nat.eq_dec i 0 then 0 else rate*x (i-1)%nat.
Proof.
  intro Hi; unfold chain_transition; destruct (Nat.eq_dec i 0) as [->|Hne].
  - clear Hi; induction m; cbn [finite_r_sum]; [reflexivity|rewrite IHm; ring].
  - apply weighted_delta; lia.
Qed.

Lemma derive_nonnegative (pre : PFormula D) c gamma :
  hoare_derivable pre c (PFLe (PConst 0) (PProb gamma)).
Proof.
  eapply derive_post; [apply derive_true|].
  intros ps Hps H; apply measure_nonnegative.
Qed.

Lemma chain_lower m k (beta gamma : CFormula D) body regions rate solution exits :
  (k < m)%nat ->
  while_regions_in_guard m beta regions -> while_regions_disjoint m regions ->
  (forall i, (i < m)%nat -> 0 < exits i \/ ((0 < i)%nat /\ 0 < rate)) ->
  (forall i, (i < m)%nat -> (0 < i)%nat ->
    hoare_derivable (p_concentrated_unit (regions i)) body
      (PFLe (PConst rate) (PProb (regions (i-1)%nat)))) ->
  (forall i, (i < m)%nat ->
    hoare_derivable (p_concentrated_unit (regions i)) body
      (PFLe (PConst (exits i)) (PProb (c_and (c_not beta) gamma)))) ->
  (forall i, (i < m)%nat ->
    solution i <= (if Nat.eq_dec i 0 then 0 else rate*solution (i-1)%nat) + exits i /\
    0 <= solution i <= 1) ->
  hoare_derivable (p_concentrated_unit (regions k)) (CWhile beta body)
    (PFLe (PConst (solution k)) (PProb gamma)).
Proof.
  intros Hk Hg Hd Hp Hstep Hexit Hsol.
  apply (lower_unit m k beta gamma body regions solution exits (chain_transition rate));
    try assumption.
  - intros i Hi; destruct (Hp i Hi) as [H|[H Hrate]]; [left; exact H|].
    right; exists (i-1)%nat; split; [lia|]. unfold chain_transition.
    destruct (Nat.eq_dec i 0); [lia|]. destruct (Nat.eq_dec (i-1) (i-1)); [exact Hrate|lia].
  - intros i Hi; apply HAnd; [apply derive_finite_and|apply Hexit; exact Hi].
    intros j Hj; unfold chain_transition.
    destruct (Nat.eq_dec i 0); [apply derive_nonnegative|].
    destruct (Nat.eq_dec j (i-1)) as [->|Hne];
      [apply Hstep; lia|apply derive_nonnegative].
  - intros i Hi; rewrite (chain_sum m i rate solution Hi); apply Hsol; exact Hi.
Qed.

Lemma mass_disjoint_union ps (A B : CFormula D) : pstate_admissible ps ->
  cformula_valid (c_not (c_and A B)) ->
  mass ps (c_or A B) = mass ps A + mass ps B.
Proof.
  intros Hps Hdis; unfold mass; cbn [pterm_eval].
  rewrite (measure_extensional _ _ (fun w => satisfies w A \/ satisfies w B)).
  - apply measure_additive; [exact (ConcreteMeasure.subprob_finite Hps)|].
    intros w H; apply (Hdis w); apply satisfies_and; exact H.
  - intro w; unfold formula_assertion; apply satisfies_or.
Qed.

Definition exact_partition (A B : CFormula D) x :=
  p_and (p_eq (PProb A) (PConst x))
    (p_and (p_eq (PProb B) (PConst (1-x))) (p_concentrated_unit (c_or A B))).

Lemma complementary_lower pre c (A B : CFormula D) x :
  cformula_valid (c_not (c_and A B)) ->
  hoare_derivable pre c (PFLe (PConst x) (PProb A)) ->
  hoare_derivable pre c (PFLe (PConst (1-x)) (PProb B)) ->
  hoare_derivable pre c (exact_partition A B x).
Proof.
  intros Hd H1 H2. eapply derive_post; [apply HAnd; [exact H1|exact H2]|].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [Ha Hb].
  change (x <= mass ps A) in Ha. change (1-x <= mass ps B) in Hb.
  pose proof (mass_disjoint_union ps A B Hps Hd) as Hu.
  pose proof (mass_mono ps (c_or A B) c_true Hps (fun w _ => satisfies_true w)) as Hm.
  pose proof (mass_true_le ps Hps) as Ht.
  unfold exact_partition; apply psatisfies_and; split;
    [apply psatisfies_eq; change (mass ps A = x); lra|].
  apply psatisfies_and; split;
    [apply psatisfies_eq; change (mass ps B = 1-x); lra|].
  apply psatisfies_and; split; [apply psatisfies_almost_sure|apply psatisfies_eq];
    change (mass ps (c_or A B) = mass ps c_true) || change (mass ps c_true = 1); lra.
Qed.

Lemma lower_subset pre c (A B : CFormula D) x :
  (forall w, satisfies w A -> satisfies w B) ->
  hoare_derivable pre c (PFLe (PConst x) (PProb A)) ->
  hoare_derivable pre c (PFLe (PConst x) (PProb B)).
Proof.
  intros Hsub H. eapply derive_post; [exact H|].
  intros ps Hps Hout. pose proof (mass_mono ps A B Hps Hsub).
  change (x <= mass ps A) in Hout. change (x <= mass ps B); lra.
Qed.

End LoopCertificates.

Lemma unit_partition_sum {D} (ps : Pstate D) support pivot :
  pstate_admissible ps -> psatisfies ps (p_concentrated_unit support) ->
  mass ps pivot + mass ps (c_not pivot) = 1.
Proof.
  intros Hps Hunit.
  pose proof (mass_split ps c_true pivot Hps) as Hsplit.
  apply psatisfies_and in Hunit; destruct Hunit as [Hs Hmass].
  apply psatisfies_eq in Hmass.
  rewrite (mass_ext ps (c_and pivot c_true) pivot),
    (mass_ext ps (c_and (c_not pivot) c_true) (c_not pivot)) in Hsplit;
    try (intro w; rewrite satisfies_and; cbn; tauto).
  change (mass ps c_true = 1) in Hmass; lra.
Qed.

(** * Protocol and specifications *)
Definition seq_v := dom_program_var "seq".
Definition exp_v := dom_program_var "exp".
Definition time_v := dom_program_var "t".
Definition remaining_v := dom_program_var "n".
Definition retries_v := dom_program_var "r".
Definition fail_v := bool_program_var "fail".
Definition acked_v := bool_program_var "acked".
Definition lostD_v := bool_program_var "lostD".
Definition lostA_v := bool_program_var "lostA".
Definition start_seq := dom_logic_var "s".
Definition start_time := dom_logic_var "t0".

Definition num (n : nat) : Term nat_domain := TConst (D := nat_domain) n.
Definition var (x : DomProgramVar) : Term nat_domain := TProgVar x.
Definition add : Term nat_domain -> Term nat_domain -> Term nat_domain := TOp (D := nat_domain) NAdd.
Definition eqn : Term nat_domain -> Term nat_domain -> CFormula nat_domain := FRel (D := nat_domain) NEq.
Definition le : Term nat_domain -> Term nat_domain -> CFormula nat_domain := FRel (D := nat_domain) NLe.
Definition lt : Term nat_domain -> Term nat_domain -> CFormula nat_domain := FRel (D := nat_domain) NLt.
Definition flag (x : BoolProgramVar) : CFormula nat_domain := FProgBool x.
Definition all (gs : list (CFormula nat_domain)) := fold_right c_and c_true gs.

Definition inner_guard K := c_and (c_not (flag acked_v)) (lt (var retries_v) (num K)).
Definition outer_guard := c_and (lt (num 0) (var remaining_v)) (c_not (flag fail_v)).

Definition attempt (p q : R) : Cmd nat_domain :=
  CSeq (CBoolToss lostD_v p)
    (CSeq
      (CIf (c_not (flag lostD_v))
        (CSeq
          (CIf (eqn (var seq_v) (var exp_v))
            (CDomAssign exp_v (add (var exp_v) (num 1))) CSkip)
          (CSeq (CBoolToss lostA_v q)
            (CIf (c_not (flag lostA_v)) (CBoolAssign acked_v c_true) CSkip)))
        CSkip)
      (CSeq (CDomAssign retries_v (add (var retries_v) (num 1)))
        (CDomAssign time_v (add (var time_v) (num 1))))).

Definition finish_chunk : Cmd nat_domain :=
  CIf (flag acked_v)
    (CSeq (CDomAssign seq_v (add (var seq_v) (num 1)))
      (CDomAssign remaining_v (TOp (D := nat_domain) NSub (var remaining_v) (num 1))))
    (CBoolAssign fail_v c_true).

Definition chunk K p q : Cmd nat_domain :=
  CSeq (CDomAssign retries_v (num 0))
    (CSeq (CBoolAssign acked_v FFalse)
      (CSeq (CWhile (inner_guard K) (attempt p q)) finish_chunk)).

Definition program K p q : Cmd nat_domain :=
  CSeq (CBoolAssign fail_v FFalse) (CWhile outer_guard (chunk K p q)).

Definition rho p q := (1-p)*(1-q).
Definition sigma K p q := 1-(1-rho p q)^K.

Definition initial N : CFormula nat_domain := all
  [eqn (var seq_v) (TLogicVar start_seq);
   eqn (var exp_v) (TLogicVar start_seq);
   eqn (var time_v) (TLogicVar start_time);
   eqn (var remaining_v) (num N)].
Definition pre N := p_eq (PProb (initial N)) (PConst 1).

Definition success K N : CFormula nat_domain := all
  [c_not (flag fail_v);
   eqn (var seq_v) (add (TLogicVar start_seq) (num N));
   eqn (var exp_v) (add (TLogicVar start_seq) (num N));
   le (var time_v) (add (TLogicVar start_time) (num (K*N)))].
Definition receiver_safe : CFormula nat_domain :=
  c_or (eqn (var exp_v) (var seq_v))
    (eqn (var exp_v) (add (var seq_v) (num 1))).
Definition unacked_delivery : CFormula nat_domain :=
  c_and (c_not (flag fail_v)) (c_not (eqn (var exp_v) (var seq_v))).
Definition fast N : CFormula nat_domain :=
  c_and (c_not (flag fail_v))
    (eqn (var time_v) (add (TLogicVar start_time) (num N))).

Definition success_post K N p q := p_eq (PProb (success K N)) (PConst (sigma K p q ^ N)).
Definition safety_post := p_and
  (p_eq (PProb receiver_safe) (PConst 1))
  (p_eq (PProb unacked_delivery) (PConst 0)).
Definition fast_post N p q := p_eq (PProb (fast N)) (PConst (rho p q ^ N)).

Definition outer_region K N c : CFormula nat_domain := all
  [c_not (flag fail_v);
   eqn (var seq_v) (add (TLogicVar start_seq) (num c));
   eqn (var exp_v) (var seq_v);
   eqn (var remaining_v) (num (N-c));
   le (add (TLogicVar start_time) (num c)) (var time_v);
   le (var time_v) (add (TLogicVar start_time) (num (K*c)))].

Definition inner_region K N c j : CFormula nat_domain := all
  [c_not (flag fail_v); c_not (flag acked_v);
   eqn (var seq_v) (add (TLogicVar start_seq) (num c));
   receiver_safe;
   eqn (var remaining_v) (num (N-c)); eqn (var retries_v) (num j);
   le (add (TLogicVar start_time) (num (c+j))) (var time_v);
   le (var time_v) (add (TLogicVar start_time) (num (K*c+j)))].

Definition chunk_good K N c : CFormula nat_domain := all
  [c_not (flag fail_v);
   eqn (var seq_v) (add (TLogicVar start_seq) (num c));
   receiver_safe;
   FImpl (flag acked_v) (eqn (var exp_v) (add (var seq_v) (num 1)));
   eqn (var remaining_v) (num (N-c));
   le (add (TLogicVar start_time) (num (c+1))) (var time_v);
   le (var time_v) (add (TLogicVar start_time) (num (K*(c+1))))].
Definition chunk_ack K N c := c_and (flag acked_v) (chunk_good K N c).
Definition chunk_exhausted K N c :=
  c_and (c_not (flag acked_v))
    (c_and (eqn (var retries_v) (num K)) (chunk_good K N c)).

Lemma satisfies_all w gs : satisfies w (all gs) <-> Forall (satisfies w) gs.
Proof.
  induction gs as [|g gs IH].
  - split; intros; [constructor|apply satisfies_true].
  - change (satisfies w (c_and g (all gs)) <-> Forall (satisfies w) (g :: gs)).
    rewrite satisfies_and, IH; split; intro H; [constructor; tauto|inversion H; tauto].
Qed.

Ltac state_simpl Hw :=
  unfold inner_region, outer_region, inner_guard, outer_guard,
    chunk_ack, chunk_exhausted, chunk_good, receiver_safe, initial, success,
    unacked_delivery, fast, eqn, le, lt, add, var, num, flag, all in Hw |- *;
  cbn [fold_right] in Hw |- *;
  repeat first
    [ progress (rewrite !satisfies_and in Hw)
    | progress (rewrite !satisfies_and)
    | progress (rewrite !satisfies_or in Hw)
    | progress (rewrite !satisfies_or)
    | progress (rewrite !subst_dom_cformula_correct)
    | progress (rewrite !subst_bool_cformula_correct) ];
  cbn [satisfies term_eval cformula_eval_bool c_true c_not c_and c_iff
    dom_program_values bool_program_values dom_logic_values bool_logic_values
    dom_op_eval dom_rel_eval implb nat_rel_eval nat_op_eval nat_domain update_dom update_bool
    dom_program_var_eq_dec bool_program_var_eq_dec
    seq_v exp_v time_v remaining_v retries_v fail_v acked_v lostD_v lostA_v] in Hw |- *;
  repeat rewrite Nat.eqb_eq in Hw; repeat rewrite Nat.eqb_eq;
  repeat rewrite Nat.leb_le in Hw; repeat rewrite Nat.leb_le;
  repeat rewrite Nat.ltb_lt in Hw; repeat rewrite Nat.ltb_lt.

Lemma attempt_loop_free p q : 0 <= p <= 1 -> 0 <= q <= 1 -> loop_free (attempt p q).
Proof. intros Hp Hq; unfold attempt; cbn [loop_free]; unfold coin_probability_valid; tauto. Qed.

Lemma finish_loop_free : loop_free finish_chunk.
Proof. cbn [finish_chunk loop_free]; tauto. Qed.

Ltac support_arithmetic Hw :=
  state_simpl Hw;
  repeat rewrite satisfies_and in Hw; repeat rewrite satisfies_and;
  repeat rewrite satisfies_or in Hw; repeat rewrite satisfies_or;
  cbn [satisfies term_eval nat_rel_eval nat_op_eval nat_domain] in Hw |- *;
  repeat rewrite Nat.eqb_eq in Hw; repeat rewrite Nat.eqb_eq;
  repeat rewrite Nat.leb_le in Hw; repeat rewrite Nat.leb_le;
  repeat rewrite Nat.ltb_lt in Hw; repeat rewrite Nat.ltb_lt;

  repeat match goal with
  | |- context [bool_program_var_eq_dec ?x ?y] =>
      let Edec := fresh "Edec" in destruct (bool_program_var_eq_dec x y) as [Edec|Edec];
        [try (discriminate Edec)|try (exfalso; apply Edec; reflexivity)]
  | |- context [dom_program_var_eq_dec ?x ?y] =>
      let Edec := fresh "Edec" in destruct (dom_program_var_eq_dec x y) as [Edec|Edec];
        [try (discriminate Edec)|try (exfalso; apply Edec; reflexivity)]
  end;
  cbn in Hw |- *;
  repeat rewrite Nat.mul_add_distr_l; repeat rewrite Nat.mul_1_r;
  intuition (try congruence; lia).

(** * Shared deterministic outcomes of a transmission attempt *)
Definition attempt_tick gamma :=
  subst_dom_cformula retries_v (add (var retries_v) (num 1))
    (subst_dom_cformula time_v (add (var time_v) (num 1)) gamma).
Definition attempt_reply (a : bool) gamma :=
  subst_bool_cformula lostA_v (if a then c_true else FFalse)
    (if a then attempt_tick gamma
     else subst_bool_cformula acked_v c_true (attempt_tick gamma)).
Definition attempt_pullback (d a : bool) gamma :=
  subst_bool_cformula lostD_v (if d then c_true else FFalse)
    (if d then attempt_tick gamma else
      c_or (c_and (eqn (var seq_v) (var exp_v))
              (subst_dom_cformula exp_v (add (var exp_v) (num 1)) (attempt_reply a gamma)))
           (c_and (c_not (eqn (var seq_v) (var exp_v))) (attempt_reply a gamma))).

Ltac branch_simpl :=
  repeat first [rewrite subst_bool_cformula_correct |
    rewrite subst_dom_cformula_correct | rewrite satisfies_and |
    rewrite satisfies_or | rewrite satisfies_not];
  cbn [satisfies flag eqn var add num term_eval nat_rel_eval nat_op_eval
    nat_domain cformula_eval_bool c_true bool_program_values dom_program_values
    update_bool update_dom bool_program_var_eq_dec dom_program_var_eq_dec
    lostD_v lostA_v acked_v seq_v exp_v retries_v time_v];
  cbn; repeat match goal with
  | |- context [bool_program_var_eq_dec ?x ?y] =>
      destruct (bool_program_var_eq_dec x y); [try discriminate | try congruence]
  | |- context [dom_program_var_eq_dec ?x ?y] =>
      destruct (dom_program_var_eq_dec x y); [try discriminate | try congruence]
  end; cbn.

(** Normalize the random attempt once, for an arbitrary output event. *)
Lemma attempt_preterm p q gamma ps : pstate_admissible ps ->
  pterm_eval (preterm (attempt p q) gamma) ps =
    p * mass ps (attempt_pullback true true gamma) +
    (1-p)*q * mass ps (attempt_pullback false true gamma) +
    rho p q * mass ps (attempt_pullback false false gamma).
Proof.
  intro Hps.
  rewrite (mass_split ps (attempt_pullback false true gamma)
    (eqn (var seq_v) (var exp_v)) Hps),
    (mass_split ps (attempt_pullback false false gamma)
    (eqn (var seq_v) (var exp_v)) Hps).
  remember (mass ps (attempt_pullback true true gamma)) as md eqn:ED.
  remember (mass ps (c_and (eqn (var seq_v) (var exp_v))
    (attempt_pullback false true gamma))) as ma1 eqn:EA1.
  remember (mass ps (c_and (c_not (eqn (var seq_v) (var exp_v)))
    (attempt_pullback false true gamma))) as ma0 eqn:EA0.
  remember (mass ps (c_and (eqn (var seq_v) (var exp_v))
    (attempt_pullback false false gamma))) as ms1 eqn:ES1.
  remember (mass ps (c_and (c_not (eqn (var seq_v) (var exp_v)))
    (attempt_pullback false false gamma))) as ms0 eqn:ES0.
  cbn [attempt preterm lift_preterm subst_dom_pterm subst_bool_pterm
    condition_pterm toss_pterm pterm_eval].
  repeat match goal with
  | |- context [measure_of (pstate_measure ps) (formula_assertion ?g)] =>
      let E := fresh "branch_event" in
      first
        [ assert (E : mass ps g = 0) by
            (transitivity (mass ps FFalse); [apply mass_ext; intro w;
              branch_simpl; intuition discriminate | apply mass_false])
        | multimatch goal with
          | HE : ?v = mass ps ?event |- _ =>
            assert (E : mass ps g = v) by
              (rewrite HE; apply mass_ext; intro w;
                unfold attempt_pullback, attempt_reply, attempt_tick;
                branch_simpl; intuition discriminate)
          end ];
      cbn [mass pterm_eval] in E; rewrite E; clear E
  end.
  unfold rho; ring.
Qed.


Definition attempt_state (d a : bool) (w : state nat_domain) :=
  let wd := update_bool w lostD_v d in
  let received :=
    if Nat.eqb (dom_program_values w seq_v) (dom_program_values w exp_v)
    then update_dom wd exp_v (dom_program_values w exp_v + 1)%nat else wd in
  let wa := update_bool received lostA_v a in
  let replied := if a then wa else update_bool wa acked_v true in
  let result := if d then wd else replied in
  update_dom (update_dom result retries_v (dom_program_values w retries_v + 1)%nat)
    time_v (dom_program_values w time_v + 1)%nat.

Lemma attempt_pullback_correct d a gamma w :
  satisfies w (attempt_pullback d a gamma) <-> satisfies (attempt_state d a w) gamma.
Proof.
  destruct d, a; unfold attempt_pullback, attempt_reply, attempt_tick, attempt_state;
    branch_simpl; try (intuition discriminate);
    destruct (Nat.eqb (dom_program_values w seq_v)
      (dom_program_values w exp_v)) eqn:E;
    cbn; intuition discriminate.
Qed.

Lemma attempt_branch_unit d a gamma ps S b : pstate_admissible ps ->
  psatisfies ps (p_concentrated_unit S) ->
  (forall w, satisfies w S -> (satisfies (attempt_state d a w) gamma <-> b = true)) ->
  mass ps (attempt_pullback d a gamma) = if b then 1 else 0.
Proof.
  intros Hps HS H.
  apply (mass_on_unit ps S _ b Hps HS); intros w Hw.
  rewrite attempt_pullback_correct; apply H; exact Hw.
Qed.

Lemma attempt_exact S gamma p q (bd ba bs : bool) : 0<=p<1 -> 0<=q<1 ->
  (forall w, satisfies w S -> (satisfies (attempt_state true true w) gamma <-> bd = true)) ->
  (forall w, satisfies w S -> (satisfies (attempt_state false true w) gamma <-> ba = true)) ->
  (forall w, satisfies w S -> (satisfies (attempt_state false false w) gamma <-> bs = true)) ->
  hoare_derivable (p_concentrated_unit S) (attempt p q)
    (p_eq (PProb gamma) (PConst
      (p*(if bd then 1 else 0)+(1-p)*q*(if ba then 1 else 0)+rho p q*(if bs then 1 else 0)))).
Proof.
  intros Hp Hq HD HA HS; apply loop_free_exact; [apply attempt_loop_free; lra|].
  intros ps Hps HU; rewrite attempt_preterm by exact Hps.
  rewrite (attempt_branch_unit _ _ _ ps S bd Hps HU HD),
    (attempt_branch_unit _ _ _ ps S ba Hps HU HA),
    (attempt_branch_unit _ _ _ ps S bs Hps HU HS); reflexivity.
Qed.

(** Common post-state facts for the bounded-retry rules. *)
Definition attempt_outcome K N c j (d a : bool) :=
  if orb d a then inner_region K N c (S j)
  else c_and (chunk_ack K N c) (eqn (var retries_v) (num (S j))).

Ltac attempt_arithmetic w Hw :=
  unfold attempt_state;
  let E := fresh "received" in
  destruct (Nat.eqb (dom_program_values w seq_v) (dom_program_values w exp_v)) eqn:E;
  [apply Nat.eqb_eq in E | apply Nat.eqb_neq in E];
  support_arithmetic Hw.

Lemma attempt_outcome_state K N c j d a : (j<K)%nat ->
  forall w, satisfies w (inner_region K N c j) ->
  satisfies (attempt_state d a w) (attempt_outcome K N c j d a).
Proof.
  intros Hj w Hw; destruct d, a; unfold attempt_outcome; cbn [orb];
    attempt_arithmetic w Hw.
Qed.

Ltac use_attempt_outcome K N c j Hj :=
  intros w Hw;
  match goal with
  | |- satisfies (attempt_state ?d ?a w) _ <-> _ =>
      let HS := fresh "outcome" in
      pose proof (attempt_outcome_state K N c j d a Hj w Hw) as HS;
      generalize HS; generalize (attempt_state d a w); intros out Hout;
      unfold attempt_outcome in Hout; cbn [orb] in Hout;
      support_arithmetic Hout
  end.
Lemma attempt_ack K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> (j < K)%nat ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j)) (attempt p q)
    (p_eq (PProb (c_and (c_not (inner_guard K)) (chunk_ack K N c))) (PConst (rho p q))).
Proof.
  intros Hp Hq Hj.
  replace (rho p q) with (p*0+(1-p)*q*0+rho p q*1) by ring.
  apply (attempt_exact _ _ p q false false true Hp Hq);
    use_attempt_outcome K N c j Hj.
Qed.

Lemma attempt_continue K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> (S j < K)%nat ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j)) (attempt p q)
    (p_eq (PProb (inner_region K N c (S j))) (PConst (1-rho p q))).
Proof.
  intros Hp Hq Hj; assert (HjK : (j<K)%nat) by lia.
  replace (1-rho p q) with (p*1+(1-p)*q*1+rho p q*0) by (unfold rho; ring).
  apply (attempt_exact _ _ p q true true false Hp Hq);
    use_attempt_outcome K N c j HjK.
Qed.

Lemma attempt_exhausted K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> S j = K ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j)) (attempt p q)
    (p_eq (PProb (c_and (c_not (inner_guard K)) (chunk_exhausted K N c)))
      (PConst (1-rho p q))).
Proof.
  intros Hp Hq Hj; assert (HjK : (j<K)%nat) by lia.
  replace (1-rho p q) with (p*1+(1-p)*q*1+rho p q*0) by (unfold rho; ring).
  apply (attempt_exact _ _ p q true true false Hp Hq);
    use_attempt_outcome K N c j HjK.
Qed.

Lemma rho_bounds p q : 0 <= p < 1 -> 0 <= q < 1 -> 0 < rho p q <= 1.
Proof. intros Hp Hq; unfold rho; nra. Qed.

Lemma power_bounds x n : 0 <= x <= 1 -> 0 <= x^n <= 1.
Proof. intro H; induction n; cbn; nra. Qed.

Lemma power_strict x n : 0 <= x < 1 -> (0 < n)%nat -> x^n < 1.
Proof.
  intros H Hn. destruct n; [lia|]. cbn.
  pose proof (power_bounds x n ltac:(lra)); nra.
Qed.

Lemma sigma_bounds K p q : 0 <= p < 1 -> 0 <= q < 1 -> 0 <= sigma K p q <= 1.
Proof.
  intros Hp Hq. pose proof (rho_bounds p q Hp Hq).
  pose proof (power_bounds (1-rho p q) K ltac:(lra)). unfold sigma; lra.
Qed.

Lemma sigma_positive K p q : (0 < K)%nat -> 0 <= p < 1 -> 0 <= q < 1 ->
  0 < sigma K p q.
Proof.
  intros HK Hp Hq. pose proof (rho_bounds p q Hp Hq).
  pose proof (power_strict (1-rho p q) K ltac:(lra) HK). unfold sigma; lra.
Qed.

Lemma inner_success_equation K j p q : (j < K)%nat ->
  1-(1-rho p q)^(K-j) =
    rho p q + (1-rho p q)*(1-(1-rho p q)^(K-S j)).
Proof.
  intro Hj. replace (K-j)%nat with (S (K-S j)) by lia. cbn; ring.
Qed.

Lemma inner_failure_equation K j p q : (j < K)%nat ->
  (1-rho p q)^(K-j) = (1-rho p q)*(1-rho p q)^(K-S j).
Proof. intro Hj; replace (K-j)%nat with (S (K-S j)) by lia; reflexivity. Qed.

Lemma outer_success_equation K N c p q : (c < N)%nat ->
  sigma K p q ^ (N-c) = sigma K p q * sigma K p q ^ (N-S c).
Proof. intro Hc; replace (N-c)%nat with (S (N-S c)) by lia; reflexivity. Qed.

Lemma outer_failure_equation K N c p q : (c < N)%nat ->
  1-sigma K p q ^ (N-c) =
    (1-sigma K p q) + sigma K p q * (1-sigma K p q ^ (N-S c)).
Proof. intro Hc; rewrite (outer_success_equation K N c p q Hc); ring. Qed.

Lemma exact_lower {D} pre cmd (A : CFormula D) x :
  hoare_derivable pre cmd (p_eq (PProb A) (PConst x)) ->
  hoare_derivable pre cmd (PFLe (PConst x) (PProb A)).
Proof.
  intro H; eapply derive_post; [exact H|].
  intros ps Hps HE; apply psatisfies_eq in HE; cbn in HE |- *; lra.
Qed.

Lemma inner_inside K N c j : (j < K)%nat ->
  forall w, satisfies w (inner_region K N c j) -> satisfies w (inner_guard K).
Proof. intros Hj w Hw; support_arithmetic Hw. Qed.

Lemma inner_disjoint K N c j k : j <> k ->
  forall w, ~ (satisfies w (inner_region K N c j) /\ satisfies w (inner_region K N c k)).
Proof.
  intros Hjk w [Hw Hk]. state_simpl Hw; state_simpl Hk; intuition lia.
Qed.

(** * Bounded retries and batch success/safety *)
Lemma inner_success_lower K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> (j < K)%nat ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j))
    (CWhile (inner_guard K) (attempt p q))
    (PFLe (PConst (1-(1-rho p q)^(K-j))) (PProb (chunk_ack K N c))).
Proof.
  intros Hp Hq Hj. pose proof (rho_bounds p q Hp Hq) as Hr.
  replace j with (K-1-(K-1-j))%nat at 1 by lia.
  replace (K-j)%nat with (S (K-1-j)) by lia.
  apply (chain_lower K (K-1-j) (inner_guard K) (chunk_ack K N c) (attempt p q)
    (fun i => inner_region K N c (K-1-i)) (1-rho p q)
    (fun i => 1-(1-rho p q)^(S i)) (fun _ => rho p q)).
  - lia.
  - intros i Hi w Hw; apply (inner_inside K N c (K-1-i) ltac:(lia) w Hw).
  - intros i k Hi Hk w H; apply satisfies_and in H;
    apply (inner_disjoint K N c (K-1-i) (K-1-k) ltac:(lia) w H).
  - intros i Hi; left; lra.
  - intros i Hi Hpos. replace (K-1-(i-1))%nat with (S (K-1-i)) by lia.
    apply exact_lower, attempt_continue; try assumption; lia.
  - intros i Hi; apply exact_lower, attempt_ack; try assumption; lia.
  - intros i Hi. pose proof (power_bounds (1-rho p q) (S i) ltac:(lra)).
    split; [|lra]. destruct (Nat.eq_dec i 0) as [->|Hne].
    + cbn; lra.
    + replace (S (i-1)) with i by lia. destruct i; [lia|]. cbn; nra.
Qed.

Lemma inner_failure_lower K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> (j < K)%nat ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j))
    (CWhile (inner_guard K) (attempt p q))
    (PFLe (PConst ((1-rho p q)^(K-j))) (PProb (chunk_exhausted K N c))).
Proof.
  intros Hp Hq Hj. pose proof (rho_bounds p q Hp Hq) as Hr.
  destruct (Req_dec (1-rho p q) 0) as [Hz|Hnz].
  { rewrite Hz. replace (K-j)%nat with (S (K-S j)) by lia.
    cbn; rewrite Rmult_0_l; apply derive_nonnegative. }
  replace j with (K-1-(K-1-j))%nat at 1 by lia.
  replace (K-j)%nat with (S (K-1-j)) by lia.
  apply (chain_lower K (K-1-j) (inner_guard K) (chunk_exhausted K N c) (attempt p q)
    (fun i => inner_region K N c (K-1-i)) (1-rho p q)
    (fun i => (1-rho p q)^(S i)) (fun i => if Nat.eq_dec i 0 then 1-rho p q else 0)).
  - lia.
  - intros i Hi w Hw; apply (inner_inside K N c (K-1-i) ltac:(lia) w Hw).
  - intros i k Hi Hk w H; apply satisfies_and in H;
    apply (inner_disjoint K N c (K-1-i) (K-1-k) ltac:(lia) w H).
  - intros i Hi; destruct (Nat.eq_dec i 0); [left; lra|right; split; [lia|lra]].
  - intros i Hi Hpos. replace (K-1-(i-1))%nat with (S (K-1-i)) by lia.
    apply exact_lower, attempt_continue; try assumption; lia.
  - intros i Hi; destruct (Nat.eq_dec i 0) as [->|Hne].
    + apply exact_lower, attempt_exhausted; try assumption; lia.
    + apply derive_nonnegative.
  - intros i Hi. pose proof (power_bounds (1-rho p q) (S i) ltac:(lra)).
    split; [|lra]. destruct (Nat.eq_dec i 0) as [->|Hne].
    + cbn; lra.
    + replace (S (i-1)) with i by lia. destruct i; [lia|]. cbn; nra.
Qed.

Lemma inner_exact K N c j p q :
  0 <= p < 1 -> 0 <= q < 1 -> (j < K)%nat ->
  hoare_derivable (p_concentrated_unit (inner_region K N c j))
    (CWhile (inner_guard K) (attempt p q))
    (exact_partition (chunk_ack K N c) (chunk_exhausted K N c)
      (1-(1-rho p q)^(K-j))).
Proof.
  intros Hp Hq Hj. apply complementary_lower.
  - intros w H; apply satisfies_and in H; destruct H as [HA HB].
    unfold chunk_ack, chunk_exhausted in HA, HB; rewrite satisfies_and in HA, HB;
      cbn in HB; tauto.
  - apply inner_success_lower; assumption.
  - replace (1-(1-(1-rho p q)^(K-j))) with ((1-rho p q)^(K-j)) by ring.
    apply inner_failure_lower; assumption.
Qed.

Definition failure : CFormula nat_domain := c_and (flag fail_v) receiver_safe.

Lemma dom_assign_unit {D} x value (A B : CFormula D) :
  (forall w, satisfies w A -> satisfies (update_dom w x (term_eval value w)) B) ->
  hoare_derivable (p_concentrated_unit A) (CDomAssign x value) (p_concentrated_unit B).
Proof.
  intro H. eapply derive_pre; [|apply HDomAssign].
  intros ps Hps Hpre; apply psatisfies_and in Hpre; destruct Hpre as [Hs Hm].
  change (psatisfies ps (p_concentrated_unit (subst_dom_cformula x value B))).
  apply psatisfies_and; split; [|exact Hm]. apply psatisfies_almost_sure.
  apply (mass_on_support ps A _ c_true Hps Hs).
  intros w Hw; rewrite subst_dom_cformula_correct; split;
    [intros _; apply satisfies_true|intros _; apply H; exact Hw].
Qed.

Definition finish_state (w : state nat_domain) :=
  if bool_program_values w acked_v then
    update_dom (update_dom w seq_v (dom_program_values w seq_v + 1)%nat)
      remaining_v (dom_program_values w remaining_v - 1)%nat
  else update_bool w fail_v true.

(** A deterministic finish maps an output event to one input event. *)
Lemma finish_preterm_event ps gamma S pivot : pstate_admissible ps ->
  psatisfies ps (p_concentrated_unit S) ->
  (forall w, satisfies w S ->
    (satisfies (finish_state w) gamma <-> satisfies w pivot)) ->
  pterm_eval (preterm finish_chunk gamma) ps = mass ps pivot.
Proof.
  intros Hps HU H; apply psatisfies_and in HU; destruct HU as [HU _].
  cbn [finish_chunk preterm lift_preterm subst_dom_pterm subst_bool_pterm
    condition_pterm pterm_eval].
  rewrite (mass_split ps pivot (flag acked_v) Hps).
  apply f_equal2; apply (mass_on_support ps S _ _ Hps HU);
    intros w Hw; specialize (H w Hw); unfold finish_state in H;
    branch_simpl; destruct (bool_program_values w acked_v); cbn in H |- *;
    intuition discriminate.
Qed.

Ltac finish_event ps Hps HS support pivot arithmetic :=
  rewrite (finish_preterm_event ps _ support pivot Hps HS);
  [|intros w Hw; unfold finish_state;
    destruct (bool_program_values w acked_v) eqn:E; arithmetic Hw].

Ltac finish_probability K N c p q pivot :=
  intros ps Hps HP;
  unfold exact_partition in HP;
  apply psatisfies_and in HP; destruct HP as [HA HP];
  apply psatisfies_and in HP; destruct HP as [HB HU];
  apply psatisfies_eq in HA, HB;
  finish_event ps Hps HU (c_or (chunk_ack K N c) (chunk_exhausted K N c))
    pivot ltac:(fun H => support_arithmetic H);
  assumption.

Lemma finish_ack K N c p q : (c < N)%nat ->
  hoare_derivable (exact_partition (chunk_ack K N c) (chunk_exhausted K N c) (sigma K p q))
    finish_chunk (p_eq (PProb (outer_region K N (S c))) (PConst (sigma K p q))).
Proof.
  intro Hc. apply loop_free_exact; [apply finish_loop_free|].
  finish_probability K N c p q (chunk_ack K N c).
Qed.

Lemma finish_failure K N c p q : (c < N)%nat ->
  hoare_derivable (exact_partition (chunk_ack K N c) (chunk_exhausted K N c) (sigma K p q))
    finish_chunk (p_eq (PProb failure) (PConst (1-sigma K p q))).
Proof.
  intro Hc. apply loop_free_exact; [apply finish_loop_free|].
  unfold failure. finish_probability K N c p q (chunk_exhausted K N c).
Qed.

Lemma chunk_exact K N c p q :
  (0 < K)%nat -> (c < N)%nat -> 0 <= p < 1 -> 0 <= q < 1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N c)) (chunk K p q)
    (exact_partition (outer_region K N (S c)) failure (sigma K p q)).
Proof.
  intros HK Hc Hp Hq. unfold chunk.
  eapply HSeq with (eta2 := p_concentrated_unit
    (c_and (outer_region K N c) (eqn (var retries_v) (num 0)))).
  - apply dom_assign_unit; intros w Hw; support_arithmetic Hw.
  - eapply HSeq with (eta2 := p_concentrated_unit (inner_region K N c 0)).
    + apply assign_unit; intros w Hw; support_arithmetic Hw.
    + eapply HSeq with (eta2 := exact_partition (chunk_ack K N c)
        (chunk_exhausted K N c) (sigma K p q)).
      * unfold sigma. pose proof (inner_exact K N c 0 p q Hp Hq HK) as H.
        rewrite Nat.sub_0_r in H; exact H.
      * apply complementary_lower.
        -- intros w H; apply satisfies_and in H; destruct H as [Hw HF].
           unfold failure in HF; apply satisfies_and in HF; destruct HF as [HF _].
           state_simpl Hw; cbn in HF; tauto.
        -- apply exact_lower, finish_ack; assumption.
        -- apply exact_lower, finish_failure; assumption.
Qed.

Lemma chunk_next_lower K N c p q :
  (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N c)) (chunk K p q)
    (PFLe (PConst (sigma K p q)) (PProb (outer_region K N (S c)))).
Proof.
  intros HK Hc Hp Hq. apply exact_lower.
  eapply derive_post; [apply chunk_exact; assumption|].
  intros ps Hps H; unfold exact_partition in H; apply psatisfies_and in H; tauto.
Qed.

Lemma chunk_failure_lower K N c p q :
  (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N c)) (chunk K p q)
    (PFLe (PConst (1-sigma K p q)) (PProb failure)).
Proof.
  intros HK Hc Hp Hq. apply exact_lower.
  eapply derive_post; [apply chunk_exact; assumption|].
  intros ps Hps H; unfold exact_partition in H; rewrite !psatisfies_and in H; tauto.
Qed.

Lemma outer_inside K N c : (c<N)%nat ->
  forall w, satisfies w (outer_region K N c) -> satisfies w outer_guard.
Proof. intros Hc w Hw; support_arithmetic Hw. Qed.

Lemma outer_disjoint K N c d : (c<N)%nat -> (d<N)%nat -> c<>d ->
  forall w, ~ (satisfies w (outer_region K N c) /\ satisfies w (outer_region K N d)).
Proof.
  intros Hc Hd Hcd w [Hw Hv]; state_simpl Hw; state_simpl Hv; intuition lia.
Qed.

Lemma outer_success_lower K N c p q :
  (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N c))
    (CWhile outer_guard (chunk K p q))
    (PFLe (PConst (sigma K p q^(N-c))) (PProb (outer_region K N N))).
Proof.
  intros HK Hc Hp Hq.
  pose proof (sigma_bounds K p q Hp Hq) as Hs.
  pose proof (sigma_positive K p q HK Hp Hq) as Hpos.
  replace c with (N-1-(N-1-c))%nat at 1 by lia.
  replace (N-c)%nat with (S (N-1-c)) by lia.
  apply (chain_lower N (N-1-c) outer_guard (outer_region K N N) (chunk K p q)
    (fun i => outer_region K N (N-1-i)) (sigma K p q)
    (fun i => sigma K p q^(S i)) (fun i => if Nat.eq_dec i 0 then sigma K p q else 0)).
  - lia.
  - intros i Hi w Hw; apply (outer_inside K N (N-1-i) ltac:(lia) w Hw).
  - intros i k Hi Hk w H; apply satisfies_and in H;
    apply (outer_disjoint K N (N-1-i) (N-1-k) ltac:(lia) ltac:(lia) ltac:(lia) w H).
  - intros i Hi; destruct (Nat.eq_dec i 0); [left|right; split]; auto; lia.
  - intros i Hi Hpositive. replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_next_lower; try assumption; lia.
  - intros i Hi; destruct (Nat.eq_dec i 0) as [->|Hne].
    + eapply lower_subset; [|apply chunk_next_lower; try assumption; lia].
      replace (S (N-1-0)) with N by lia.
      intros w Hw; apply satisfies_and; split; [|exact Hw]. support_arithmetic Hw.
    + apply derive_nonnegative.
  - intros i Hi; split; [|apply power_bounds; exact Hs].
    destruct (Nat.eq_dec i 0) as [->|Hne].
    + cbn; lra.
    + replace (S (i-1)) with i by lia. destruct i; [lia|]. cbn; lra.
Qed.

Lemma outer_failure_lower K N c p q :
  (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N c))
    (CWhile outer_guard (chunk K p q))
    (PFLe (PConst (1-sigma K p q^(N-c))) (PProb failure)).
Proof.
  intros HK Hc Hp Hq. pose proof (sigma_bounds K p q Hp Hq) as Hs.
  pose proof (sigma_positive K p q HK Hp Hq) as Hpos.
  destruct (Req_dec (sigma K p q) 1) as [Heq|Hne].
  { rewrite Heq, pow1; replace (1-1) with 0 by ring; apply derive_nonnegative. }
  replace c with (N-1-(N-1-c))%nat at 1 by lia.
  replace (N-c)%nat with (S (N-1-c)) by lia.
  apply (chain_lower N (N-1-c) outer_guard failure (chunk K p q)
    (fun i => outer_region K N (N-1-i)) (sigma K p q)
    (fun i => 1-sigma K p q^(S i)) (fun _ => 1-sigma K p q)).
  - lia.
  - intros i Hi w Hw; apply (outer_inside K N (N-1-i) ltac:(lia) w Hw).
  - intros i k Hi Hk w H; apply satisfies_and in H;
    apply (outer_disjoint K N (N-1-i) (N-1-k) ltac:(lia) ltac:(lia) ltac:(lia) w H).
  - intros i Hi; left; lra.
  - intros i Hi Hpositive. replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_next_lower; try assumption; lia.
  - intros i Hi. eapply lower_subset; [|apply chunk_failure_lower; try assumption; lia].
    intros w Hw; apply satisfies_and; split; [|exact Hw].
    unfold failure in Hw; apply satisfies_and in Hw; destruct Hw as [HF _].
    change (~ satisfies w outer_guard).
    unfold outer_guard; rewrite satisfies_and; cbn in HF |- *; tauto.
  - intros i Hi. pose proof (power_bounds (sigma K p q) (S i) Hs).
    split; [|lra]. destruct (Nat.eq_dec i 0) as [->|Hni].
    + cbn; lra.
    + replace (S (i-1)) with i by lia. destruct i; [lia|]. cbn; nra.
Qed.

Lemma outer_exact K N p q :
  (0<K)%nat -> (0<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (outer_region K N 0))
    (CWhile outer_guard (chunk K p q))
    (exact_partition (outer_region K N N) failure (sigma K p q^N)).
Proof.
  intros HK HN Hp Hq. apply complementary_lower.
  - intros w H; apply satisfies_and in H; destruct H as [Hw HF].
    unfold failure in HF; apply satisfies_and in HF; destruct HF as [HF _].
    state_simpl Hw; cbn in HF; tauto.
  - pose proof (outer_success_lower K N 0 p q HK HN Hp Hq) as H.
    rewrite Nat.sub_0_r in H; exact H.
  - pose proof (outer_failure_lower K N 0 p q HK HN Hp Hq) as H.
    rewrite Nat.sub_0_r in H; exact H.
Qed.

Lemma initial_reset K N :
  hoare_derivable (pre N) (CBoolAssign fail_v FFalse)
    (p_concentrated_unit (outer_region K N 0)).
Proof.
  eapply derive_pre; [|apply assign_unit with (A := initial N)].
  - intros ps Hps H; apply unit_of_probability_one; assumption.
  - intros w Hw; support_arithmetic Hw.
Qed.

Definition batch_post K N p q := p_and (success_post K N p q) safety_post.

Lemma partition_implies_batch_post K N p q ps : pstate_admissible ps ->
  psatisfies ps (exact_partition (outer_region K N N) failure (sigma K p q^N)) ->
  psatisfies ps (batch_post K N p q).
Proof.
  intros Hps H; unfold exact_partition in H.
  apply psatisfies_and in H; destruct H as [HS H].
  apply psatisfies_and in H; destruct H as [HF H].
  apply psatisfies_and in H; destruct H as [HU HM].
  apply psatisfies_eq in HS, HF, HM.
  assert (ES : mass ps (success K N) = mass ps (outer_region K N N)).
  { apply (mass_on_support ps (c_or (outer_region K N N) failure) _ _ Hps HU).
    intros w Hw; unfold failure in Hw; support_arithmetic Hw. }
  assert (ER : mass ps receiver_safe = 1).
  { apply (mass_on_unit ps (c_or (outer_region K N N) failure) receiver_safe true Hps).
    - apply psatisfies_and; split; [exact HU|apply psatisfies_eq; exact HM].
    - intros w Hw; unfold failure in Hw; support_arithmetic Hw. }
  assert (EU : mass ps unacked_delivery = 0).
  { apply (mass_on_unit ps (c_or (outer_region K N N) failure) unacked_delivery false Hps).
    - apply psatisfies_and; split; [exact HU|apply psatisfies_eq; exact HM].
    - intros w Hw; unfold failure in Hw; support_arithmetic Hw. }
  unfold batch_post, success_post, safety_post.
  apply psatisfies_and; split.
  - apply psatisfies_eq; change (mass ps (success K N) = sigma K p q^N).
    rewrite ES; exact HS.
  - apply psatisfies_and; split; apply psatisfies_eq; assumption.
Qed.

Theorem batch_transfer_positive K N p q :
  (0<K)%nat -> (0<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (pre N) (program K p q) (batch_post K N p q).
Proof.
  intros HK HN Hp Hq. unfold program.
  eapply HSeq; [apply initial_reset|].
  eapply derive_post; [apply outer_exact; assumption|].
  intros ps Hps H; apply partition_implies_batch_post; assumption.
Qed.

Lemma unit_partition {D} (A B : CFormula D) ps : pstate_admissible ps ->
  (forall w, satisfies w A -> ~ satisfies w B) ->
  psatisfies ps (p_concentrated_unit A) -> psatisfies ps (exact_partition A B 1).
Proof.
  intros Hps Hd HU.
  assert (HA : mass ps A = 1).
  { apply (mass_on_unit ps A A true Hps HU); intros w Hw; cbn; tauto. }
  assert (HB : mass ps B = 0).
  { apply (mass_on_unit ps A B false Hps HU); intros w Hw; specialize (Hd w Hw); cbn; intuition discriminate. }
  unfold exact_partition; apply psatisfies_and; split; [apply psatisfies_eq; exact HA|].
  apply psatisfies_and; split; [apply psatisfies_eq; change (mass ps B = 1-1); lra|].
  apply unit_of_probability_one; [exact Hps|].
  apply psatisfies_eq; apply (mass_on_unit ps A (c_or A B) true Hps HU).
  intros w Hw; rewrite satisfies_or; cbn; tauto.
Qed.

Theorem batch_transfer_empty K p q :
  hoare_derivable (pre 0) (program K p q) (batch_post K 0 p q).
Proof.
  unfold program. eapply HSeq; [apply (initial_reset K 0)|].
  eapply derive_post; [apply while_not_unit with (gamma := outer_region K 0 0)|].
  - intros w Hw; support_arithmetic Hw.
  - intros ps Hps HP. apply partition_implies_batch_post.
    + exact Hps.
    + cbn [pow]. apply unit_partition; [exact Hps| |apply unit_of_probability_one; assumption].
      intros w Hw HB. unfold failure in HB; apply satisfies_and in HB; destruct HB as [HB _].
      state_simpl Hw; cbn in HB; tauto.
Qed.

Lemma zero_chunk N p q :
  hoare_derivable (p_concentrated_unit (outer_region 0 N 0)) (chunk 0 p q)
    (p_eq (PProb failure) (PConst 1)).
Proof.
  unfold chunk. eapply HSeq with (eta2 := p_concentrated_unit
    (c_and (outer_region 0 N 0) (eqn (var retries_v) (num 0)))).
  - apply dom_assign_unit; intros w Hw; support_arithmetic Hw.
  - eapply HSeq with (eta2 := p_concentrated_unit (inner_region 0 N 0 0)).
    + apply assign_unit; intros w Hw; support_arithmetic Hw.
    + eapply HSeq with (eta2 := p_concentrated_unit (inner_region 0 N 0 0)).
      * eapply derive_post; [apply while_not_unit with (gamma := inner_region 0 N 0 0)|].
        -- intros w Hw; split; [support_arithmetic Hw|exact Hw].
        -- intros ps Hps H; apply unit_of_probability_one; assumption.
      * apply loop_free_exact; [apply finish_loop_free|].
        intros ps Hps HU.
        unfold failure.
        finish_event ps Hps HU (inner_region 0 N 0 0) (c_true (D := nat_domain))
          ltac:(fun H => support_arithmetic H).
        apply psatisfies_and in HU; destruct HU as [_ HM];
        apply psatisfies_eq in HM; exact HM.
Qed.

Theorem batch_transfer_zero_attempts N p q : (0<N)%nat ->
  hoare_derivable (pre N) (program 0 p q) (batch_post 0 N p q).
Proof.
  intro HN. unfold program. eapply HSeq; [apply (initial_reset 0 N)|].
  eapply derive_post with (post := exact_partition (outer_region 0 N N) failure 0).
  - apply complementary_lower.
    + intros w H; apply satisfies_and in H; destruct H as [Hw HF].
      unfold failure in HF; apply satisfies_and in HF; destruct HF as [HF _].
      state_simpl Hw; cbn in HF; tauto.
    + apply derive_nonnegative.
    + replace (1-0) with 1 by ring.
      apply (chain_lower 1 0 outer_guard failure (chunk 0 p q)
        (fun _ => outer_region 0 N 0) 0 (fun _ => 1) (fun _ => 1)).
      * lia.
      * intros i Hi w Hw; apply (outer_inside 0 N 0 HN w Hw).
      * intros i j Hi Hj; lia.
      * intros; left; lra.
      * intros i Hi Hpos; lia.
      * intros i Hi. eapply lower_subset; [|apply exact_lower, zero_chunk].
        intros w Hw; apply satisfies_and; split; [|exact Hw].
        unfold failure in Hw; apply satisfies_and in Hw; destruct Hw as [HF _].
        change (~ satisfies w outer_guard).
    unfold outer_guard; rewrite satisfies_and; cbn in HF |- *; tauto.
      * intros i Hi; assert (i=0)%nat by lia; subst; cbn; lra.
  - intros ps Hps H. apply partition_implies_batch_post; [exact Hps|].
    unfold sigma; cbn. replace (1-1) with 0 by ring.
    destruct N; [lia|]. cbn; rewrite Rmult_0_l; exact H.
Qed.

(** Exact success probability and both receiver-safety assertions, including
    empty batches and zero permitted attempts. *)
Theorem batch_transfer K N p q : 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (pre N) (program K p q) (batch_post K N p q).
Proof.
  intros Hp Hq; destruct N as [|N].
  - apply batch_transfer_empty.
  - destruct K as [|K].
    + apply batch_transfer_zero_attempts; lia.
    + apply batch_transfer_positive; try assumption; lia.
Qed.

End BatchTransfer.

(** * Fast-path timing *)
Module BatchTransferTiming.
Import BatchTransfer.

Definition retry_positive := lt (num 0) (var retries_v).
Definition clock_mode c (late : bool) : CFormula nat_domain :=
  if late then le (add (TLogicVar start_time) (add (num (S c)) (var retries_v))) (var time_v)
  else eqn (var time_v) (add (TLogicVar start_time) (add (num c) (var retries_v))).
Definition timed_region K N c (late : bool) := c_and (outer_region K N c)
  (if late then lt (add (TLogicVar start_time) (num c)) (var time_v)
   else eqn (var time_v) (add (TLogicVar start_time) (num c))).
Definition timed_inner K N c j late := c_and (inner_region K N c j) (clock_mode c late).
Definition first_ack := c_and (flag acked_v) (eqn (var retries_v) (num 1)).

Ltac timing_arithmetic Hw :=
  unfold timed_region, timed_inner, clock_mode, retry_positive, first_ack in Hw |- *;
  support_arithmetic Hw.

Lemma unit_implies {D} ps (A B : CFormula D) : pstate_admissible ps ->
  (forall w, satisfies w A -> satisfies w B) ->
  psatisfies ps (p_concentrated_unit A) -> psatisfies ps (p_concentrated_unit B).
Proof.
  intros Hps Hsub HU. apply unit_of_probability_one; [exact Hps|].
  apply psatisfies_eq; apply (mass_on_unit ps A B true Hps HU); intros w Hw; cbn; split;
    [intros _; reflexivity|intros _; apply Hsub; exact Hw].
Qed.

Lemma strengthen_unit {D} (A B : CFormula D) cmd post :
  (forall w, satisfies w A -> satisfies w B) ->
  hoare_derivable (p_concentrated_unit B) cmd post ->
  hoare_derivable (p_concentrated_unit A) cmd post.
Proof.
  intros Hsub H. eapply derive_pre; [|exact H].
  intros ps Hps HU; apply (unit_implies ps A B Hps Hsub HU).
Qed.

Lemma lower_with_unit {D} pre cmd (A I : CFormula D) x :
  hoare_derivable pre cmd (PFLe (PConst x) (PProb A)) ->
  hoare_derivable pre cmd (p_concentrated_unit I) ->
  hoare_derivable pre cmd (PFLe (PConst x) (PProb (c_and A I))).
Proof.
  intros DA DI. eapply derive_post; [apply HAnd; [exact DA|exact DI]|].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [HA HI].
  apply psatisfies_and in HI; destruct HI as [HI _].
  change (x <= mass ps (c_and A I)); change (x <= mass ps A) in HA.
  rewrite (mass_on_support ps I (c_and A I) A Hps HI); [exact HA|].
  intros w Hw; rewrite satisfies_and; tauto.
Qed.

Lemma sum_lower {D} pre cmd (A B : CFormula D) x y :
  cformula_valid (c_not (c_and A B)) ->
  hoare_derivable pre cmd (PFLe (PConst x) (PProb A)) ->
  hoare_derivable pre cmd (PFLe (PConst y) (PProb B)) ->
  hoare_derivable pre cmd (PFLe (PConst (x+y)) (PProb (c_or A B))).
Proof.
  intros Hd DA DB. eapply derive_post; [apply HAnd; [exact DA|exact DB]|].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [HA HB].
  change (x<=mass ps A) in HA; change (y<=mass ps B) in HB.
  change (x+y<=mass ps (c_or A B)); rewrite (mass_disjoint_union ps A B Hps Hd); lra.
Qed.

Lemma attempt_clock K N c j late p q : 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c j late)) (attempt p q)
    (p_concentrated_unit (c_and (clock_mode c late) (eqn (var retries_v) (num (S j))))).
Proof.
  intros Hp Hq; eapply derive_post with (post := p_eq
    (PProb (c_and (clock_mode c late) (eqn (var retries_v) (num (S j))))) (PConst 1)).
  - replace 1 with (p*1+(1-p)*q*1+rho p q*1) by (unfold rho; ring).
    apply (attempt_exact _ _ p q true true true Hp Hq);
      intros w Hw; destruct late; unfold timed_inner, clock_mode in Hw |- *;
      attempt_arithmetic w Hw.
  - intros ps Hps H; apply unit_of_probability_one; assumption.
Qed.

Lemma attempt_clock_positive K N c j late p q : 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c j late)) (attempt p q)
    (p_concentrated_unit (c_and (clock_mode c late) retry_positive)).
Proof.
  intros Hp Hq. eapply derive_post; [apply attempt_clock; assumption|].
  intros ps Hps H; eapply unit_implies; [exact Hps| |exact H].
  intros w Hw; unfold retry_positive, eqn, var, num, lt in *.
  rewrite satisfies_and in Hw |- *; destruct Hw as [HC HR]; split; [exact HC|].
  cbn in HR |- *; apply Nat.eqb_eq in HR; rewrite HR; reflexivity.
Qed.

Lemma timed_inner_inside K N c j late : (j<K)%nat ->
  forall w, satisfies w (timed_inner K N c j late) -> satisfies w (inner_guard K).
Proof.
  intros Hj w H; apply satisfies_and in H; apply (inner_inside K N c j Hj w); tauto.
Qed.

Lemma inner_clock K N c j late p q : 0<=p<1 -> 0<=q<1 -> (j<K)%nat ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c j late))
    (CWhile (inner_guard K) (attempt p q))
    (p_concentrated_unit (c_and (clock_mode c late) retry_positive)).
Proof.
  intros Hp Hq Hj. pose proof (rho_bounds p q Hp Hq) as Hr.
  eapply derive_post with (post := PFLe (PConst 1)
    (PProb (c_and (clock_mode c late) retry_positive))).
  - replace j with (K-1-(K-1-j))%nat at 1 by lia.
    apply (chain_lower K (K-1-j) (inner_guard K)
      (c_and (clock_mode c late) retry_positive) (attempt p q)
      (fun i => timed_inner K N c (K-1-i) late) (1-rho p q)
      (fun _ => 1) (fun i => if Nat.eq_dec i 0 then 1 else rho p q)).
    + lia.
    + intros i Hi w Hw; apply (timed_inner_inside K N c (K-1-i) late ltac:(lia) w Hw).
    + intros i k Hi Hk w H; apply satisfies_and in H; destruct H as [Hiw Hkw].
      apply satisfies_and in Hiw, Hkw.
      apply (inner_disjoint K N c (K-1-i) (K-1-k) ltac:(lia) w); tauto.
    + intros i Hi; left; destruct (Nat.eq_dec i 0); lra.
    + intros i Hi Hpos. replace (K-1-(i-1))%nat with (S (K-1-i)) by lia.
      unfold timed_inner at 2.
      eapply lower_subset; [|eapply lower_with_unit with (A := inner_region K N c (S (K-1-i))) (I := c_and (clock_mode c late) retry_positive)].
      * intros w H; repeat rewrite satisfies_and in H; repeat rewrite satisfies_and; tauto.
      * eapply strengthen_unit; [|apply exact_lower, attempt_continue; try assumption; lia].
        intros w H; apply satisfies_and in H; tauto.
      * apply attempt_clock_positive; assumption.
    + intros i Hi; destruct (Nat.eq_dec i 0) as [->|Hne].
      * replace 1 with (rho p q + (1-rho p q)) by ring.
        eapply lower_subset; [|eapply lower_with_unit with (A := c_or (c_and (c_not (inner_guard K)) (chunk_ack K N c)) (c_and (c_not (inner_guard K)) (chunk_exhausted K N c))) (I := c_and (clock_mode c late) retry_positive)].
        -- intros w H; rewrite satisfies_and in H; destruct H as [HE HI].
           apply satisfies_or in HE; apply satisfies_and; split; [|exact HI].
           destruct HE as [HE|HE]; apply satisfies_and in HE; tauto.
        -- apply sum_lower.
           ++ intros w H; rewrite !satisfies_and in H.
              unfold chunk_ack, chunk_exhausted in H; repeat rewrite satisfies_and in H; cbn in H; tauto.
           ++ eapply strengthen_unit with (B := inner_region K N c (K-1-0)); [|apply exact_lower, attempt_ack; try assumption; lia].
              intros w H; apply satisfies_and in H; tauto.
           ++ eapply strengthen_unit with (B := inner_region K N c (K-1-0)); [|apply exact_lower, attempt_exhausted; try assumption; lia].
              intros w H; apply satisfies_and in H; tauto.
        -- apply attempt_clock_positive; assumption.
      * eapply lower_subset; [|eapply lower_with_unit with (A := c_and (c_not (inner_guard K)) (chunk_ack K N c)) (I := c_and (clock_mode c late) retry_positive)].
        -- intros w H; repeat rewrite satisfies_and in H; repeat rewrite satisfies_and; tauto.
        -- eapply strengthen_unit with (B := inner_region K N c (K-1-i)); [|apply exact_lower, attempt_ack; try assumption; lia].
           intros w H; apply satisfies_and in H; tauto.
        -- apply attempt_clock_positive; assumption.
    + intros i Hi; destruct (Nat.eq_dec i 0); cbn; split; lra.
  - intros ps Hps H. apply unit_of_probability_one; [exact Hps|].
    change (1 <= mass ps (c_and (clock_mode c late) retry_positive)) in H.
    pose proof (mass_mono ps (c_and (clock_mode c late) retry_positive) c_true Hps
      (fun w _ => satisfies_true w)). pose proof (mass_true_le ps Hps).
    apply psatisfies_eq; change (mass ps (c_and (clock_mode c late) retry_positive)=1); lra.
Qed.

Lemma upper_unit {D} m k (beta gamma : CFormula D) body regions solution exits transitions :
  (k<m)%nat -> while_regions_cover m beta regions ->
  (forall i, (i<m)%nat -> hoare_derivable (p_concentrated_unit (regions i)) body
    (while_body_post_upper m regions (transitions i) beta gamma (exits i))) ->
  while_upper_solution m solution transitions exits ->
  hoare_derivable (p_concentrated_unit (c_and beta (regions k))) (CWhile beta body)
    (PFLe (PProb gamma) (PConst (solution k))).
Proof.
  intros Hk Hcover Hbody Hsol. set (y := prob_logic_var "upper_mass").
  with_unit_mass (p_concentrated_unit (c_and beta (regions k))) (CWhile beta body)
    (PFLe (PProb gamma) (PConst (solution k)))
    (PFLe (PProb gamma) (PMul (PConst (solution k)) (PVar y))) y.
  eapply derive_pre; [|exact (HWhileUpper m k beta gamma body regions solution exits
    transitions y Hk Hcover Hbody Hsol)].
  intros ps Hps H; apply psatisfies_and in H; destruct H as [HU Hy].
  apply psatisfies_and in HU; destruct HU as [Hs Hm].
  apply psatisfies_eq in Hm, Hy. apply psatisfies_and; split; [exact Hs|].
  cbn in Hm, Hy |- *; lra.
Qed.

Definition retry_zero := eqn (var retries_v) (num 0).
Definition attempt_prefix p q : Cmd nat_domain :=
  CSeq (CBoolToss lostD_v p)
      (CIf (c_not (flag lostD_v))
        (CSeq
          (CIf (eqn (var seq_v) (var exp_v))
            (CDomAssign exp_v (add (var exp_v) (num 1))) CSkip)
          (CSeq (CBoolToss lostA_v q)
            (CIf (c_not (flag lostA_v)) (CBoolAssign acked_v c_true) CSkip))) CSkip).

Lemma attempt_nonzero pre K p q :
  hoare_derivable pre (attempt p q)
    (p_eq (PProb (c_and (inner_guard K) retry_zero)) (PConst 0)).
Proof.
  eapply derive_post with (post := p_eq (PProb retry_zero) (PConst 0)).
  - unfold attempt. eapply HSeq with (eta2 := p_true); [apply derive_true|].
    eapply HSeq with (eta2 := p_true); [apply derive_true|].
    apply loop_free_exact; [cbn [loop_free]; tauto|].
    intros ps Hps H; cbn [preterm lift_preterm subst_dom_pterm pterm_eval].
    match goal with |- measure_of _ (formula_assertion ?target)=0 =>
      change (mass ps target=0)
    end.
    transitivity (mass ps FFalse); [|apply mass_false].
    apply mass_ext; intros w; repeat rewrite subst_dom_cformula_correct.
    unfold retry_zero; assert (Hw : satisfies w c_true) by apply satisfies_true;
    timing_arithmetic Hw.
  - intros ps Hps H; apply psatisfies_eq in H; apply psatisfies_eq.
    pose proof (mass_mono ps (c_and (inner_guard K) retry_zero) retry_zero Hps
      ltac:(intros w Hw; apply satisfies_and in Hw; tauto)).
    pose proof (mass_nonneg ps (c_and (inner_guard K) retry_zero)).
    change (mass ps retry_zero=0) in H.
    change (mass ps (c_and (inner_guard K) retry_zero)=0); lra.
Qed.

Lemma attempt_first_upper_row K p q : 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (c_and (inner_guard K) retry_zero))
    (attempt p q) (p_eq (PProb (c_and (c_not (inner_guard K)) first_ack)) (PConst (rho p q))).
Proof.
  intros Hp Hq.
  replace (rho p q) with (p*0+(1-p)*q*0+rho p q*1) by ring.
  apply (attempt_exact _ _ p q false false true Hp Hq);
    intros w Hw; unfold retry_zero, first_ack in Hw |- *;
    attempt_arithmetic w Hw.
Qed.

Lemma attempt_not_first K p q : 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (c_and (inner_guard K) (c_not retry_zero)))
    (attempt p q) (p_eq (PProb (c_and (c_not (inner_guard K)) first_ack)) (PConst 0)).
Proof.
  intros Hp Hq.
  replace 0 with (p*0+(1-p)*q*0+rho p q*0) by ring.
  apply (attempt_exact _ _ p q false false false Hp Hq);
    intros w Hw; unfold retry_zero, first_ack in Hw |- *;
    attempt_arithmetic w Hw.
Qed.

Lemma derive_upper_one {D} pre cmd (A : CFormula D) :
  hoare_derivable pre cmd (PFLe (PProb A) (PConst 1)).
Proof.
  eapply derive_post; [apply derive_true|].
  intros ps Hps H. pose proof (mass_mono ps A c_true Hps (fun w _ => satisfies_true w)).
  pose proof (mass_true_le ps Hps); change (mass ps A<=1); lra.
Qed.

Lemma exact_upper {D} pre cmd (A : CFormula D) x :
  hoare_derivable pre cmd (p_eq (PProb A) (PConst x)) ->
  hoare_derivable pre cmd (PFLe (PProb A) (PConst x)).
Proof.
  intro H; eapply derive_post; [exact H|].
  intros ps Hps HE; apply psatisfies_eq in HE; cbn in HE |- *; lra.
Qed.

Lemma inner_first_upper K N c p q : (0<K)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c 0 false))
    (CWhile (inner_guard K) (attempt p q)) (PFLe (PProb first_ack) (PConst (rho p q))).
Proof.
  intros HK Hp Hq. pose proof (rho_bounds p q Hp Hq) as Hr.
  set (regions := fun i => c_and (inner_guard K)
    (if Nat.eqb i 0 then retry_zero else c_not retry_zero)).
  eapply strengthen_unit with (B := c_and (inner_guard K) (regions 0%nat)).
  - intros w Hw; unfold regions, retry_zero; cbn [Nat.eqb]. timing_arithmetic Hw.
  - apply (upper_unit 2 0 (inner_guard K) first_ack (attempt p q) regions
      (fun i => if Nat.eqb i 0 then rho p q else 0)
      (fun i => if Nat.eqb i 0 then rho p q else 0)
      (fun _ j => if Nat.eqb j 0 then 0 else 1)).
    + lia.
    + intros w Hw.
      change (satisfies w (c_or (c_or FFalse (c_and (inner_guard K) retry_zero))
        (c_and (inner_guard K) (c_not retry_zero)))).
      repeat rewrite satisfies_or; repeat rewrite satisfies_and.
      destruct (satisfies_dec w retry_zero); cbn in *; tauto.
    + intros i Hi; apply HAnd.
      * apply derive_finite_and; intros j Hj; destruct j as [|j].
        -- cbn [Nat.eqb]; apply exact_upper, attempt_nonzero.
        -- assert (j=0)%nat by lia; subst; cbn [Nat.eqb]; apply derive_upper_one.
      * unfold regions; destruct (Nat.eqb i 0).
        -- apply exact_upper, attempt_first_upper_row; assumption.
        -- apply exact_upper, attempt_not_first; assumption.
    + intros i Hi; cbn [finite_r_sum Nat.eqb]; destruct (Nat.eqb i 0); split; lra.
Qed.

Lemma inner_first_lower K N c p q : (0<K)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c 0 false))
    (CWhile (inner_guard K) (attempt p q))
    (PFLe (PConst (rho p q))
      (PProb (c_and (chunk_ack K N c) (eqn (var retries_v) (num 1))))).
Proof.
  intros HK Hp Hq. pose proof (rho_bounds p q Hp Hq) as Hr.
  apply (chain_lower 1 0 (inner_guard K)
    (c_and (chunk_ack K N c) (eqn (var retries_v) (num 1))) (attempt p q)
    (fun _ => timed_inner K N c 0 false) 0 (fun _ => rho p q) (fun _ => rho p q)).
  - lia.
  - intros i Hi w Hw; apply (timed_inner_inside K N c 0 false HK w Hw).
  - intros i j Hi Hj; lia.
  - intros; left; lra.
  - intros i Hi Hpos; lia.
  - intros i Hi. eapply lower_subset; [|eapply lower_with_unit with (A := c_and (c_not (inner_guard K)) (chunk_ack K N c)) (I := c_and (clock_mode c false) (eqn (var retries_v) (num 1)))].
    + intros w H; repeat rewrite satisfies_and in H; repeat rewrite satisfies_and; tauto.
    + eapply strengthen_unit with (B := inner_region K N c 0); [|apply exact_lower, attempt_ack; assumption].
      intros w H; apply satisfies_and in H; tauto.
    + apply attempt_clock; assumption.
  - intros i Hi; assert (i=0)%nat by lia; subst; cbn; split; lra.
Qed.

Lemma unit_and {D} ps (A B : CFormula D) : pstate_admissible ps ->
  psatisfies ps (p_concentrated_unit A) -> psatisfies ps (p_concentrated_unit B) ->
  psatisfies ps (p_concentrated_unit (c_and A B)).
Proof.
  intros Hps HA HB. pose proof (proj1 (proj1 (psatisfies_and ps _ _) HA)) as HAs.
  apply unit_of_probability_one; [exact Hps|]. apply psatisfies_eq.
  change (mass ps (c_and A B)=1).
  rewrite (mass_on_support ps A (c_and A B) B Hps HAs).
  - apply (mass_on_unit ps B B true Hps HB); intros w Hw; cbn; tauto.
  - intros w Hw; rewrite satisfies_and; tauto.
Qed.

Definition timed_post K N c late p q :=
  p_and (exact_partition (chunk_ack K N c) (chunk_exhausted K N c) (sigma K p q))
    (p_and (p_concentrated_unit (c_and (clock_mode c late) retry_positive))
      (if late then p_true else p_eq (PProb first_ack) (PConst (rho p q)))).

Lemma inner_timing K N c late p q : (0<K)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_inner K N c 0 late))
    (CWhile (inner_guard K) (attempt p q)) (timed_post K N c late p q).
Proof.
  intros HK Hp Hq. unfold timed_post; apply HAnd.
  - eapply strengthen_unit with (B := inner_region K N c 0).
    + intros w H; apply satisfies_and in H; tauto.
    + pose proof (inner_exact K N c 0 p q Hp Hq HK) as H; rewrite Nat.sub_0_r in H; exact H.
  - apply HAnd; [apply inner_clock; assumption|].
    destruct late; [apply derive_true|].
    eapply derive_post; [apply HAnd; [apply inner_first_lower|apply inner_first_upper]; assumption|].
    intros ps Hps H; apply psatisfies_and in H; destruct H as [HL HU].
    pose proof (mass_mono ps (c_and (chunk_ack K N c) (eqn (var retries_v) (num 1)))
      first_ack Hps ltac:(intros w Hw; unfold first_ack, chunk_ack in *;
        repeat rewrite satisfies_and in Hw; repeat rewrite satisfies_and; tauto)).
    change (rho p q<=mass ps (c_and (chunk_ack K N c) (eqn (var retries_v) (num 1)))) in HL.
    change (mass ps first_ack<=rho p q) in HU.
    apply psatisfies_eq; change (mass ps first_ack=rho p q); lra.
Qed.

Definition late_ack K N c := c_and (chunk_ack K N c) (c_not (eqn (var retries_v) (num 1))).
Definition timing_support K N c late :=
  c_and (c_or (chunk_ack K N c) (chunk_exhausted K N c))
    (c_and (clock_mode c late) retry_positive).

Ltac timing_arithmetic Hw ::=
  unfold timing_support, late_ack, timed_region, timed_inner, clock_mode,
    retry_positive, first_ack in Hw |- *; support_arithmetic Hw.

Ltac timing_setup :=
  intros ps Hps HP;
  unfold timed_post in HP; apply psatisfies_and in HP; destruct HP as [HP HC];
  apply psatisfies_and in HC; destruct HC as [HC HE];
  unfold exact_partition in HP; apply psatisfies_and in HP; destruct HP as [HA HP];
  apply psatisfies_and in HP; destruct HP as [HB HU];
  pose proof (unit_and ps _ _ Hps HU HC) as HS;
  apply psatisfies_eq in HA, HB.

Ltac finish_timing_normalize ps Hps HS support pivot :=
  finish_event ps Hps HS support pivot ltac:(fun H => timing_arithmetic H).

Lemma finish_slow K N c p q : (c<N)%nat ->
  hoare_derivable (timed_post K N c true p q) finish_chunk
    (p_eq (PProb (timed_region K N (S c) true)) (PConst (sigma K p q))).
Proof.
  intro Hc; apply loop_free_exact; [apply finish_loop_free|].
  timing_setup.
  finish_timing_normalize ps Hps HS (timing_support K N c true) (chunk_ack K N c).
  exact HA.
Qed.

Lemma finish_fast K N c p q : (c<N)%nat ->
  hoare_derivable (timed_post K N c false p q) finish_chunk
    (p_eq (PProb (timed_region K N (S c) false)) (PConst (rho p q))).
Proof.
  intro Hc; apply loop_free_exact; [apply finish_loop_free|].
  timing_setup; apply psatisfies_eq in HE.
  finish_timing_normalize ps Hps HS (timing_support K N c false) first_ack.
  exact HE.
Qed.

Lemma finish_late K N c p q : (c<N)%nat ->
  hoare_derivable (timed_post K N c false p q) finish_chunk
    (p_eq (PProb (timed_region K N (S c) true)) (PConst (sigma K p q-rho p q))).
Proof.
  intro Hc; apply loop_free_exact; [apply finish_loop_free|].
  timing_setup; apply psatisfies_eq in HE.
  assert (HL : mass ps (late_ack K N c)=sigma K p q-rho p q).
  { pose proof (mass_split ps (chunk_ack K N c) (eqn (var retries_v) (num 1)) Hps) as Hsplit.
    pose proof (proj1 (proj1 (psatisfies_and ps _ _) HU)) as Hsupport.
    assert (E1 : mass ps (c_and (eqn (var retries_v) (num 1)) (chunk_ack K N c))=mass ps first_ack).
    { apply (mass_on_support ps (c_or (chunk_ack K N c) (chunk_exhausted K N c)) _ _ Hps Hsupport).
      intros w Hw; timing_arithmetic Hw. }
    assert (E2 : mass ps (c_and (c_not (eqn (var retries_v) (num 1))) (chunk_ack K N c))=
      mass ps (late_ack K N c)).
    { apply mass_ext; intros w; unfold late_ack; rewrite !satisfies_and; tauto. }
    rewrite E1, E2 in Hsplit.
    change (mass ps (chunk_ack K N c)=sigma K p q) in HA.
    change (mass ps first_ack=rho p q) in HE; lra. }
  finish_timing_normalize ps Hps HS (timing_support K N c false) (late_ack K N c).
  exact HL.
Qed.

Lemma timed_chunk_rule K N c late p q post : (0<K)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (timed_post K N c late p q) finish_chunk post ->
  hoare_derivable (p_concentrated_unit (timed_region K N c late)) (chunk K p q) post.
Proof.
  intros HK Hp Hq Hfinish. unfold chunk.
  eapply HSeq with (eta2 := p_concentrated_unit
    (c_and (timed_region K N c late) (eqn (var retries_v) (num 0)))).
  - apply dom_assign_unit; intros w Hw; destruct late; timing_arithmetic Hw.
  - eapply HSeq with (eta2 := p_concentrated_unit (timed_inner K N c 0 late)).
    + apply assign_unit; intros w Hw; destruct late; timing_arithmetic Hw.
    + eapply HSeq; [apply inner_timing; assumption|exact Hfinish].
Qed.

Lemma chunk_slow K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c true)) (chunk K p q)
    (PFLe (PConst (sigma K p q)) (PProb (timed_region K N (S c) true))).
Proof. intros; apply exact_lower, timed_chunk_rule; try assumption; apply finish_slow; assumption. Qed.
Lemma chunk_fast K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c false)) (chunk K p q)
    (PFLe (PConst (rho p q)) (PProb (timed_region K N (S c) false))).
Proof. intros; apply exact_lower, timed_chunk_rule; try assumption; apply finish_fast; assumption. Qed.
Lemma chunk_late K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c false)) (chunk K p q)
    (PFLe (PConst (sigma K p q-rho p q)) (PProb (timed_region K N (S c) true))).
Proof. intros; apply exact_lower, timed_chunk_rule; try assumption; apply finish_late; assumption. Qed.
Lemma timed_chunk_failure K N c late p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c late)) (chunk K p q)
    (PFLe (PConst (1-sigma K p q)) (PProb failure)).
Proof.
  intros. eapply strengthen_unit with (B := outer_region K N c); [|apply chunk_failure_lower; assumption].
  intros w Hw; apply satisfies_and in Hw; tauto.
Qed.

Definition dual_regions {D} m (slow quick : nat -> CFormula D) i :=
  if lt_dec i m then slow i else quick (i-m)%nat.
Definition dual_transition m s r i j :=
  if lt_dec i m then chain_transition s i j
  else if Nat.eq_dec i m then 0
  else (if Nat.eq_dec j (i-m-1) then s-r else 0) +
       (if Nat.eq_dec j (i-1) then r else 0).
Definition dual_solution m r i := if lt_dec i m then 1 else 1-r^(S (i-m)).
Definition dual_exit m s r i := if lt_dec i m then
  (if Nat.eq_dec i 0 then 1 else 1-s)
  else (if Nat.eq_dec i m then 1-r else 1-s).

Lemma finite_plus m f g : finite_r_sum m (fun i => f i+g i)=finite_r_sum m f+finite_r_sum m g.
Proof. induction m; cbn [finite_r_sum]; [ring|rewrite IHm; ring]. Qed.
Lemma finite_ext m f g : (forall i, (i<m)%nat -> f i=g i) -> finite_r_sum m f=finite_r_sum m g.
Proof. induction m; intro H; cbn; [reflexivity|rewrite IHm, H; auto; lia]. Qed.
Lemma finite_zero m : finite_r_sum m (fun _ => 0)=0.
Proof. induction m; cbn; [reflexivity|rewrite IHm; ring]. Qed.

Lemma dual_sum m s r i x : (0<m)%nat -> (i<m+m)%nat ->
  finite_r_sum (m+m) (fun j => dual_transition m s r i j*x j)=
  if lt_dec i m then (if Nat.eq_dec i 0 then 0 else s*x (i-1)%nat)
  else if Nat.eq_dec i m then 0 else (s-r)*x (i-m-1)%nat+r*x (i-1)%nat.
Proof.
  intros Hm Hi. unfold dual_transition; destruct (lt_dec i m).
  - apply chain_sum; lia.
  - destruct (Nat.eq_dec i m).
    + transitivity (finite_r_sum (m+m) (fun _ => 0)); [apply finite_ext; intros; ring|apply finite_zero].
    + transitivity (finite_r_sum (m+m) (fun j =>
        (if Nat.eq_dec j (i-m-1) then s-r else 0)*x j+
        (if Nat.eq_dec j (i-1) then r else 0)*x j)).
      * apply finite_ext; intros; ring.
      * rewrite finite_plus, !weighted_delta by lia; reflexivity.
Qed.

Lemma dual_lower {D} m k beta gamma (body : Cmd D) slow quick s r :
  (0<m)%nat -> (k<m)%nat -> 0<s<=1 -> 0<r<1 ->
  while_regions_in_guard (m+m) beta (dual_regions m slow quick) ->
  while_regions_disjoint (m+m) (dual_regions m slow quick) ->
  (forall i, (i<m)%nat -> (0<i)%nat ->
    hoare_derivable (p_concentrated_unit (slow i)) body
      (PFLe (PConst s) (PProb (slow (i-1)%nat)))) ->
  (forall i, (i<m)%nat -> (0<i)%nat ->
    hoare_derivable (p_concentrated_unit (quick i)) body
      (PFLe (PConst r) (PProb (quick (i-1)%nat)))) ->
  (forall i, (i<m)%nat -> (0<i)%nat ->
    hoare_derivable (p_concentrated_unit (quick i)) body
      (PFLe (PConst (s-r)) (PProb (slow (i-1)%nat)))) ->
  (forall i, (i<m)%nat ->
    hoare_derivable (p_concentrated_unit (slow i)) body
      (PFLe (PConst (if Nat.eq_dec i 0 then 1 else 1-s)) (PProb (c_and (c_not beta) gamma)))) ->
  (forall i, (i<m)%nat ->
    hoare_derivable (p_concentrated_unit (quick i)) body
      (PFLe (PConst (if Nat.eq_dec i 0 then 1-r else 1-s)) (PProb (c_and (c_not beta) gamma)))) ->
  hoare_derivable (p_concentrated_unit (quick k)) (CWhile beta body)
    (PFLe (PConst (1-r^(S k))) (PProb gamma)).
Proof.
  intros Hm Hk Hs Hr Hg Hd Hslow Hquick Hlate Hes Heq.
  assert (Ereg : dual_regions m slow quick (m+k)=quick k).
  { unfold dual_regions; destruct (lt_dec (m+k) m); [lia|f_equal; lia]. }
  assert (Esol : dual_solution m r (m+k)=1-r^(S k)).
  { unfold dual_solution; destruct (lt_dec (m+k) m); [lia|f_equal; f_equal; lia]. }
  rewrite <-Ereg, <-Esol.
  apply (lower_unit (m+m) (m+k) beta gamma body (dual_regions m slow quick)
    (dual_solution m r) (dual_exit m s r) (dual_transition m s r)); try assumption.
  - lia.
  - intros i Hi. unfold dual_exit, dual_transition.
    destruct (lt_dec i m) as [Hlow|Hhigh].
    + destruct (Nat.eq_dec i 0); [left; lra|right; exists (i-1)%nat; split; [lia|]].
      unfold chain_transition; destruct (Nat.eq_dec i 0); [lia|].
      destruct (Nat.eq_dec (i-1) (i-1)); [lra|lia].
    + destruct (Nat.eq_dec i m) as [He|Hne]; [left; lra|].
      right; exists (i-1)%nat; split; [lia|].
      destruct (Nat.eq_dec (i-1) (i-m-1)); [lia|].
      destruct (Nat.eq_dec (i-1) (i-1)); [lra|lia].
  - intros i Hi; apply HAnd.
    + apply derive_finite_and; intros j Hj.
      unfold dual_transition; destruct (lt_dec i m) as [Hlow|Hhigh].
      * unfold chain_transition; destruct (Nat.eq_dec i 0); [apply derive_nonnegative|].
        destruct (Nat.eq_dec j (i-1)) as [->|Hne]; [|apply derive_nonnegative].
        unfold dual_regions; destruct (lt_dec i m); [|lia].
        destruct (lt_dec (i-1) m); [apply Hslow; lia|lia].
      * destruct (Nat.eq_dec i m); [apply derive_nonnegative|].
        destruct (Nat.eq_dec j (i-m-1)) as [Eslow|Enslow];
          destruct (Nat.eq_dec j (i-1)) as [Equick|Enquick].
        -- lia.
        -- subst j; rewrite Rplus_0_r. unfold dual_regions.
           destruct (lt_dec i m); [lia|]. destruct (lt_dec (i-m-1) m); [|lia].
           apply Hlate; lia.
        -- subst j; rewrite Rplus_0_l. unfold dual_regions.
           destruct (lt_dec i m); [lia|]. destruct (lt_dec (i-1) m); [lia|].
           replace (i-1-m)%nat with (i-m-1)%nat by lia. apply Hquick; lia.
        -- replace (0+0) with 0 by ring; apply derive_nonnegative.
    + unfold dual_regions, dual_exit; destruct (lt_dec i m).
      * apply Hes; lia.
      * destruct (Nat.eq_dec i m) as [->|Hne].
        -- replace (m-m)%nat with 0%nat by lia; apply (Heq 0%nat Hm).
        -- specialize (Heq (i-m)%nat ltac:(lia)).
           destruct (Nat.eq_dec (i-m) 0); [lia|exact Heq].
  - intros i Hi; rewrite dual_sum by lia.
    unfold dual_solution, dual_exit; destruct (lt_dec i m) as [Hlow|Hhigh].
    + destruct (Nat.eq_dec i 0) as [->|Hne]; [cbn; split; lra|].
      destruct (lt_dec (i-1) m); [split; lra|lia].
    + pose proof (power_bounds r (S (i-m)) ltac:(lra)) as Hpow.
      split; [|lra]. destruct (Nat.eq_dec i m) as [->|Hne].
      * rewrite Nat.sub_diag; cbn; lra.
      * destruct (lt_dec (i-m-1) m); [|lia].
        destruct (lt_dec (i-1) m); [lia|].
        replace (S (i-1-m)) with (i-m)%nat by lia. cbn [pow]; nra.
Qed.

Lemma timed_inside K N c late : (c<N)%nat ->
  forall w, satisfies w (timed_region K N c late) -> satisfies w outer_guard.
Proof. intros Hc w H; apply satisfies_and in H; apply (outer_inside K N c Hc w); tauto. Qed.

Lemma timed_disjoint K N c d l h : (c<N)%nat -> (d<N)%nat -> (c<>d \/ l<>h) ->
  cformula_valid (c_not (c_and (timed_region K N c l) (timed_region K N d h))).
Proof.
  intros Hc Hd Hdiff w Hw; destruct l, h; try (destruct Hdiff as [Hdiff|Hdiff]; [|contradiction]);
    timing_arithmetic Hw.
Qed.

Lemma timed_failure_disjoint K N c late :
  cformula_valid (c_not (c_and failure (timed_region K N c late))).
Proof.
  intros w H; unfold failure, timed_region in H; repeat rewrite satisfies_and in H.
  destruct H as [[HF _] [HQ _]]; state_simpl HQ; cbn in HF; tauto.
Qed.

Lemma slow_exit K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c true)) (chunk K p q)
    (PFLe (PConst (if Nat.eq_dec (S c) N then 1 else 1-sigma K p q))
      (PProb (c_and (c_not outer_guard) (c_not (fast N))))).
Proof.
  intros HK Hc Hp Hq; destruct (Nat.eq_dec (S c) N) as [He|Hne].
  - replace 1 with ((1-sigma K p q)+sigma K p q) by ring.
    eapply lower_subset with (A := c_or failure (timed_region K N (S c) true)).
    + intros w Hw; unfold failure in Hw; timing_arithmetic Hw.
    + apply sum_lower; [apply timed_failure_disjoint| |].
      * apply timed_chunk_failure; assumption.
      * apply chunk_slow; assumption.
  - eapply lower_subset with (A := failure).
    + intros w Hw; unfold failure in Hw; timing_arithmetic Hw.
    + apply timed_chunk_failure; assumption.
Qed.

Lemma quick_exit K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c false)) (chunk K p q)
    (PFLe (PConst (if Nat.eq_dec (S c) N then 1-rho p q else 1-sigma K p q))
      (PProb (c_and (c_not outer_guard) (c_not (fast N))))).
Proof.
  intros HK Hc Hp Hq; destruct (Nat.eq_dec (S c) N) as [He|Hne].
  - replace (1-rho p q) with ((1-sigma K p q)+(sigma K p q-rho p q)) by ring.
    eapply lower_subset with (A := c_or failure (timed_region K N (S c) true)).
    + intros w Hw; unfold failure in Hw; timing_arithmetic Hw.
    + apply sum_lower; [apply timed_failure_disjoint| |].
      * apply timed_chunk_failure; assumption.
      * apply chunk_late; assumption.
  - eapply lower_subset with (A := failure).
    + intros w Hw; unfold failure in Hw; timing_arithmetic Hw.
    + apply timed_chunk_failure; assumption.
Qed.

Lemma fast_loop_lower K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c false))
    (CWhile outer_guard (chunk K p q))
    (PFLe (PConst (rho p q^(N-c))) (PProb (fast N))).
Proof.
  intros HK Hc Hp Hq. pose proof (rho_bounds p q Hp Hq) as Hr.
  replace c with (N-1-(N-1-c))%nat at 1 by lia.
  replace (N-c)%nat with (S (N-1-c)) by lia.
  apply (chain_lower N (N-1-c) outer_guard (fast N) (chunk K p q)
    (fun i => timed_region K N (N-1-i) false) (rho p q)
    (fun i => rho p q^(S i)) (fun i => if Nat.eq_dec i 0 then rho p q else 0)).
  - lia.
  - intros i Hi w Hw; apply (timed_inside K N (N-1-i) false ltac:(lia) w Hw).
  - intros i j Hi Hj; apply timed_disjoint; [lia|lia|left; lia].
  - intros i Hi; destruct (Nat.eq_dec i 0); [left; lra|right; split; [lia|lra]].
  - intros i Hi Hpos; replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_fast; try assumption; lia.
  - intros i Hi; destruct (Nat.eq_dec i 0) as [->|Hne]; [|apply derive_nonnegative].
    eapply lower_subset with (A := timed_region K N (S (N-1-0)) false).
    + intros w Hw; timing_arithmetic Hw.
    + apply chunk_fast; try assumption; lia.
  - intros i Hi; split; [|apply power_bounds; lra].
    destruct (Nat.eq_dec i 0) as [->|Hne]; [cbn; lra|].
    replace (S (i-1)) with i by lia; destruct i; [lia|]; cbn; lra.
Qed.

Lemma not_fast_loop_lower K N c p q : (0<K)%nat -> (c<N)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (p_concentrated_unit (timed_region K N c false))
    (CWhile outer_guard (chunk K p q))
    (PFLe (PConst (1-rho p q^(N-c))) (PProb (c_not (fast N)))).
Proof.
  intros HK Hc Hp Hq. pose proof (rho_bounds p q Hp Hq) as Hr.
  pose proof (sigma_bounds K p q Hp Hq) as Hs.
  pose proof (sigma_positive K p q HK Hp Hq) as Hspos.
  destruct (Req_dec (rho p q) 1) as [He|Hne].
  { rewrite He, pow1; replace (1-1) with 0 by ring; apply derive_nonnegative. }
  replace c with (N-1-(N-1-c))%nat at 1 by lia.
  replace (N-c)%nat with (S (N-1-c)) by lia.
  apply (dual_lower N (N-1-c) outer_guard (c_not (fast N)) (chunk K p q)
    (fun i => timed_region K N (N-1-i) true)
    (fun i => timed_region K N (N-1-i) false) (sigma K p q) (rho p q)); try lia; try lra.
  - intros i Hi w Hw; unfold dual_regions in Hw.
    destruct (lt_dec i N).
    + apply (timed_inside K N (N-1-i) true ltac:(lia) w Hw).
    + apply (timed_inside K N (N-1-(i-N)) false ltac:(lia) w Hw).
  - intros i j Hi Hj; unfold dual_regions; destruct (lt_dec i N); destruct (lt_dec j N);
    apply timed_disjoint; try lia; try (left; lia); right; discriminate.
  - intros i Hi Hpos; replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_slow; try assumption; lia.
  - intros i Hi Hpos; replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_fast; try assumption; lia.
  - intros i Hi Hpos; replace (N-1-(i-1))%nat with (S (N-1-i)) by lia.
    apply chunk_late; try assumption; lia.
  - intros i Hi. pose proof (slow_exit K N (N-1-i) p q HK ltac:(lia) Hp Hq) as H.
    destruct (Nat.eq_dec i 0); destruct (Nat.eq_dec (S (N-1-i)) N); try lia; exact H.
  - intros i Hi. pose proof (quick_exit K N (N-1-i) p q HK ltac:(lia) Hp Hq) as H.
    destruct (Nat.eq_dec i 0); destruct (Nat.eq_dec (S (N-1-i)) N); try lia; exact H.
Qed.

Lemma timed_reset K N : hoare_derivable (pre N) (CBoolAssign fail_v FFalse)
  (p_concentrated_unit (timed_region K N 0 false)).
Proof.
  eapply derive_pre; [|apply assign_unit with (A := initial N)].
  - intros ps Hps H; apply unit_of_probability_one; assumption.
  - intros w Hw; timing_arithmetic Hw.
Qed.

(** The fast-path claim needs at least one permitted attempt per chunk. *)
Theorem batch_transfer_fast K N p q : (0<K)%nat -> 0<=p<1 -> 0<=q<1 ->
  hoare_derivable (pre N) (program K p q) (fast_post N p q).
Proof.
  intros HK Hp Hq. unfold program, fast_post.
  eapply HSeq; [apply (timed_reset K N)|].
  destruct N as [|N].
  - cbn [pow]. apply while_not_unit; intros w Hw; timing_arithmetic Hw.
  - eapply derive_post with (post := exact_partition (fast (S N)) (c_not (fast (S N))) (rho p q^(S N))).
    + apply complementary_lower.
      * intros w H; apply satisfies_and in H; cbn in H; tauto.
      * pose proof (fast_loop_lower K (S N) 0 p q HK ltac:(lia) Hp Hq) as H;
        rewrite Nat.sub_0_r in H; exact H.
      * pose proof (not_fast_loop_lower K (S N) 0 p q HK ltac:(lia) Hp Hq) as H;
        rewrite Nat.sub_0_r in H; exact H.
    + intros ps Hps H; unfold exact_partition in H; apply psatisfies_and in H; tauto.
Qed.

End BatchTransferTiming.
