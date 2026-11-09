(** The uniform dice roll [x roll k], as a derived command with a
    derivable rule.

    TPHL has no dice-roll command.  [roll c x k] implements "draw [x]
    uniformly from {0, ..., k}" with biased tosses of an auxiliary Boolean
    variable [c]: with probability 1/(k+1) set [x := 0], otherwise draw
    uniformly from {1, ..., k}; finally reset [c := ff].

    Main results:
    - [roll_mass]: after [roll c x k], for every formula [g] not mentioning
      [c], [Pr(g) = sum_{i <= k} 1/(k+1) * Pr(g[x := i])];
    - [HKRoll]: for every [k] and every postcondition [eta] not mentioning
      [c], [|- {kroll_pformula c x k eta} roll c x k {eta}], where
      [kroll_pformula] replaces each [Pr(g)] by that sum.

    The derivation goes through [loop_free_complete]: over any domain, every
    valid triple about a loop-free program is derivable.  That uses the
    certificates of the completeness proof (Lemma 25), which need no
    finiteness for loop-free programs. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL.
Require Import Soundness.StateFacts Soundness.AssertionFacts Soundness.CommandFacts
  Soundness.TransformerAssertions Soundness.StructuralRules Soundness.SplitRules.
Require Import Completeness.Interface Completeness.AtomicCertificates
  Completeness.CompositeCertificates Completeness.WeakestPrecondition.
Require Import Examples.Lib.

Open Scope R_scope.

(** * Loop-free programs: validity implies derivability *)

Section LoopFree.
Context {Dm : Domain}.

Fixpoint loop_free (c : PHL.Cmd Dm) : Prop :=
  match c with
  | CSeq c1 c2 => loop_free c1 /\ loop_free c2
  | CIf _ c1 c2 => loop_free c1 /\ loop_free c2
  | CWhile _ _ => False
  | _ => True
  end.

Lemma loop_free_certificate c : loop_free c -> exists T, certificate c T.
Proof.
  induction c as [|x t|b beta|b r|c1 IH1 c2 IH2|beta c1 IH1 c2 IH2|beta body IH]; cbn.
  - intros _; eexists; apply skip_certificate.
  - intros _; eexists; apply dom_assign_certificate.
  - intros _; eexists; apply bool_assign_certificate.
  - intros _; eexists; apply toss_certificate.
  - intros [H1 H2]. destruct (IH1 H1) as [T1 HT1], (IH2 H2) as [T2 HT2].
    eexists; apply seq_certificate; eassumption.
  - intros [H1 H2]. destruct (IH1 H1) as [T1 HT1], (IH2 H2) as [T2 HT2].
    eexists; apply if_certificate; eassumption.
  - intros [].
Qed.

Theorem loop_free_complete c pre post :
  loop_free c -> hoare_valid pre c post -> hoare_derivable pre c post.
Proof.
  intros Hc Hv. destruct (loop_free_certificate c Hc) as [T HT].
  exact (certified_relative_complete c T HT pre post Hv).
Qed.

End LoopFree.

(** * Formulas not mentioning a Boolean variable *)

Section Fresh.
Variable c : BoolProgramVar.

Fixpoint cfree (g : CFormula) : Prop :=
  match g with
  | FProgBool b => b <> c
  | FImpl g1 g2 => cfree g1 /\ cfree g2
  | _ => True
  end.

Fixpoint pfree_term (p : Pterm) : Prop :=
  match p with
  | PProb g => cfree g
  | PAdd p1 p2 | PMul p1 p2 => pfree_term p1 /\ pfree_term p2
  | _ => True
  end.

Fixpoint pfree (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 => pfree_term p1 /\ pfree_term p2
  | PFFalse => True
  | PFImpl e1 e2 => pfree e1 /\ pfree e2
  end.

Lemma subst_bool_cfree beta g : cfree g -> subst_bool_cformula c beta g = g.
Proof.
  induction g as [b|b|r t1 t2| |g1 IH1 g2 IH2]; cbn; try reflexivity.
  - intros Hb. destruct (bool_program_var_eq_dec b c); [contradiction|reflexivity].
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma subst_dom_cfree x t g : cfree g -> cfree (subst_dom_cformula x t g).
Proof. induction g; cbn; tauto. Qed.

End Fresh.

(** * The program *)

Section Roll.
Variables (c : BoolProgramVar) (x : DomProgramVar).
Implicit Types (ps : Pstate) (g h : CFormula) (t : Term) (r : R) (p : Pterm) (eta : PFormula).
Local Notation run := CommandSemantics.run.

(** Draw [x] uniformly from {j, ..., j+n}. *)
Fixpoint pick (j n : nat) : Cmd :=
  match n with
  | O => CDomAssign x (tnat j)
  | S n' =>
      CSeq (CBoolToss c (/ INR (S n)))
           (CIf (FProgBool c) (CDomAssign x (tnat j)) (pick (S j) n'))
  end.

(** [x roll k]: draw [x] uniformly from {0, ..., k}. *)
Definition roll (k : nat) : Cmd :=
  CSeq (pick 0 k) (CBoolAssign c FFalse).

Lemma roll_loop_free k : loop_free (roll k).
Proof.
  unfold roll; cbn; split; [|exact I].
  generalize 0%nat; induction k as [|k IH]; intros j; cbn; auto.
Qed.

(** * Probabilities after [roll] *)

Fixpoint sumn (f : nat -> R) (m : nat) : R :=
  match m with
  | O => 0
  | S m' => f O + sumn (fun i => f (S i)) m'
  end.

Lemma sumn_scale (a : R) (f : nat -> R) (m : nat) : a * sumn f m = sumn (fun i => a * f i) m.
Proof. revert f; induction m as [|m IH]; intros f; cbn; [lra|rewrite <- IH; lra]. Qed.

Lemma sumn_ext (f g : nat -> R) (m : nat) : (forall i, (i < m)%nat -> f i = g i) -> sumn f m = sumn g m.
Proof.
  revert f g; induction m as [|m IH]; intros f g H; cbn; [reflexivity|].
  rewrite (H O) by lia. f_equal. apply IH. intros i Hi. apply H. lia.
Qed.

Definition gx (g : CFormula) (i : nat) : CFormula := subst_dom_cformula x (tnat i) g.

Lemma Pr_restrict ps g h : Pr[pstate_restrict ps g] h = Pr[ps] (c_and g h).
Proof. exact (eq_sym (condition_pterm_correct (PProb h) g ps)). Qed.

Lemma Pr_assign ps t g : Pr[run (CDomAssign x t) ps] g = Pr[ps] (subst_dom_cformula x t g).
Proof. exact (eq_sym (subst_dom_pterm_run x t (PProb g) ps)). Qed.

Lemma Pr_toss_split ps r h : coin_probability_valid r -> pstate_admissible ps -> cfree c h ->
  Pr[run (CBoolToss c r) ps] (c_and (FProgBool c) h) = r * Pr[ps] h /\
  Pr[run (CBoolToss c r) ps] (c_and (c_not (FProgBool c)) h) = (1 - r) * Pr[ps] h.
Proof.
  intros Hr Hps Hh.
  pose proof (toss_pterm_run c (PProb (c_and (FProgBool c) h)) Hr Hps) as E1.
  pose proof (toss_pterm_run c (PProb (c_and (c_not (FProgBool c)) h)) Hr Hps) as E2.
  cbn [toss_pterm pterm_eval c_and c_not subst_bool_cformula] in E1, E2.
  destruct (bool_program_var_eq_dec c c) as [_|Hn]; [|contradiction Hn; reflexivity].
  rewrite ?(subst_bool_cfree c FFalse h Hh), ?(subst_bool_cfree c c_true h Hh) in E1, E2.
  assert (Hff : forall A, (forall v, ~ satisfies v A) -> Pr[ps] A = 0).
  { intros A HA. rewrite <- (Pr_false ps). apply Pr_ext; intro v; cbn; split; [apply HA|tauto]. }
  assert (Hh' : forall A, (forall v, satisfies v A <-> satisfies v h) -> Pr[ps] A = Pr[ps] h).
  { intros A HA. apply Pr_ext; exact HA. }
  change (pterm_eval (PProb (c_and (FProgBool c) h)) (run (CBoolToss c r) ps)) with
    (Pr[run (CBoolToss c r) ps] (c_and (FProgBool c) h)) in E1.
  change (pterm_eval (PProb (c_and (c_not (FProgBool c)) h)) (run (CBoolToss c r) ps)) with
    (Pr[run (CBoolToss c r) ps] (c_and (c_not (FProgBool c)) h)) in E2.
  rewrite <- E1, <- E2. clear E1 E2.
  split.
  - match goal with |- (1 - r) * Pr[ps] ?A + r * Pr[ps] ?B = _ =>
      assert (EA : Pr[ps] A = 0) by (apply Hff; intros v; cbn; tauto);
      assert (EB : Pr[ps] B = Pr[ps] h)
        by (apply Hh'; intros v; cbn; split; [intros Hn; apply Classical_Prop.NNPP|]; tauto);
      rewrite EA, EB; lra
    end.
  - match goal with |- (1 - r) * Pr[ps] ?A + r * Pr[ps] ?B = _ =>
      assert (EB : Pr[ps] B = 0) by (apply Hff; intros v; cbn; tauto);
      assert (EA : Pr[ps] A = Pr[ps] h)
        by (apply Hh'; intros v; cbn; split; [intros Hn; apply Classical_Prop.NNPP|]; tauto);
      rewrite EA, EB; lra
    end.
Qed.

Lemma pick_mass n : forall j ps g, pstate_admissible ps -> cfree c g ->
  Pr[run (pick j n) ps] g = sumn (fun i => / INR (S n) * Pr[ps] (gx g (j + i))) (S n).
Proof.
  induction n as [|n IH]; intros j ps g Hps Hg.
  - cbn [pick sumn]. rewrite Pr_assign. unfold gx. rewrite Nat.add_0_r.
    cbn [INR]. rewrite Rinv_1. lra.
  - cbn [pick].
    set (r := / INR (S (S n))).
    assert (Hr : coin_probability_valid r).
    { unfold coin_probability_valid, r. pose proof (pos_INR (S n)) as H0.
      rewrite S_INR. split.
      - apply Rlt_le, Rinv_0_lt_compat; lra.
      - rewrite <- Rinv_1 at 2. apply Rinv_le_contravar; lra. }
    set (ps1 := run (CBoolToss c r) ps).
    assert (Hps1 : pstate_admissible ps1) by (apply run_admissible; exact Hps).
    rewrite (proj1 (run_seq_same _ _ Hps) g).
    rewrite run_if_mass by exact Hps1.
    change (Pr[run (CDomAssign x (tnat j)) (pstate_restrict ps1 (FProgBool c))] g +
            Pr[run (pick (S j) n) (pstate_restrict ps1 (c_not (FProgBool c)))] g =
            sumn (fun i => / INR (S (S n)) * Pr[ps] (gx g (j + i))) (S (S n))).
    rewrite Pr_assign, Pr_restrict.
    rewrite IH by (try apply restrict_admissible; assumption).
    erewrite sumn_ext; [|intros i _; rewrite Pr_restrict; reflexivity].
    destruct (Pr_toss_split ps r (subst_dom_cformula x (tnat j) g) Hr Hps
                (subst_dom_cfree c x _ g Hg)) as [E1 _].
    unfold ps1 in *. rewrite E1.
    erewrite sumn_ext;
      [|intros i _; rewrite (proj2 (Pr_toss_split ps r (gx g (S j + i)) Hr Hps
                                     (subst_dom_cfree c x _ g Hg))); reflexivity].
    change (sumn (fun i => / INR (S (S n)) * Pr[ps] (gx g (j + i))) (S (S n))) with
      (/ INR (S (S n)) * Pr[ps] (gx g (j + 0)) +
       sumn (fun i => / INR (S (S n)) * Pr[ps] (gx g (j + S i))) (S n)).
    replace (sumn (fun i => / INR (S n) * ((1 - r) * Pr[ps] (gx g (S j + i)))) (S n))
      with (sumn (fun i => / INR (S (S n)) * Pr[ps] (gx g (j + S i))) (S n)).
    + unfold gx, r. rewrite Nat.add_0_r. ring.
    + apply sumn_ext; intros i _.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l.
      unfold r. rewrite !S_INR. pose proof (pos_INR n).
      field. lra.
Qed.

Theorem roll_mass k ps g : pstate_admissible ps -> cfree c g ->
  Pr[run (roll k) ps] g = sumn (fun i => / INR (S k) * Pr[ps] (gx g i)) (S k).
Proof.
  intros Hps Hg. unfold roll.
  rewrite (proj1 (run_seq_same _ _ Hps) g).
  change (Pr[run (CBoolAssign c FFalse) (run (pick 0 k) ps)] g) with
    (pterm_eval (PProb g) (run (CBoolAssign c FFalse) (run (pick 0 k) ps))).
  rewrite <- (subst_bool_pterm_run c FFalse (PProb g)). cbn [subst_bool_pterm pterm_eval].
  rewrite (subst_bool_cfree c) by exact Hg.
  rewrite pick_mass by assumption. reflexivity.
Qed.

(** * The rule *)

(** [Pr(g)] becomes [sum_{i <= k} 1/(k+1) * Pr(g[x := i])]. *)
Fixpoint roll_sum (k : nat) (g : CFormula) (m : nat) (j : nat) : Pterm :=
  match m with
  | O => PConst 0
  | S m' => PAdd (PMul (PConst (/ INR (S k))) (PProb (gx g j))) (roll_sum k g m' (S j))
  end.

Fixpoint kroll_pterm (k : nat) (p : Pterm) : Pterm :=
  match p with
  | PProb g => roll_sum k g (S k) O
  | PAdd p1 p2 => PAdd (kroll_pterm k p1) (kroll_pterm k p2)
  | PMul p1 p2 => PMul (kroll_pterm k p1) (kroll_pterm k p2)
  | _ => p
  end.

Fixpoint kroll_pformula (k : nat) (eta : PFormula) : PFormula :=
  match eta with
  | PFLe p1 p2 => PFLe (kroll_pterm k p1) (kroll_pterm k p2)
  | PFFalse => PFFalse
  | PFImpl e1 e2 => PFImpl (kroll_pformula k e1) (kroll_pformula k e2)
  end.

Lemma roll_sum_eval k g m j ps :
  pterm_eval (roll_sum k g m j) ps = sumn (fun i => / INR (S k) * Pr[ps] (gx g (j + i))) m.
Proof.
  revert j; induction m as [|m IH]; intros j; cbn [roll_sum pterm_eval sumn]; [reflexivity|].
  rewrite IH, Nat.add_0_r. f_equal. apply sumn_ext; intros i _. rewrite Nat.add_succ_r.
  reflexivity.
Qed.

Lemma kroll_pterm_eval k p ps : pstate_admissible ps -> pfree_term c p ->
  pterm_eval (kroll_pterm k p) ps = pterm_eval p (run (roll k) ps).
Proof.
  intros Hps; induction p as [y|r|g|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn [kroll_pterm pfree_term];
    try reflexivity.
  - intros Hg. rewrite roll_sum_eval. cbn [pterm_eval]. rewrite roll_mass by assumption.
    reflexivity.
  - intros [H1 H2]; cbn [pterm_eval]; rewrite IH1, IH2 by assumption; reflexivity.
  - intros [H1 H2]; cbn [pterm_eval]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma kroll_pformula_correct k eta ps : pstate_admissible ps -> pfree c eta ->
  psatisfies ps (kroll_pformula k eta) <-> psatisfies (run (roll k) ps) eta.
Proof.
  intros Hps; induction eta as [p1 p2| |e1 IH1 e2 IH2]; cbn [kroll_pformula pfree psatisfies].
  - intros [H1 H2]; rewrite !kroll_pterm_eval by assumption; reflexivity.
  - tauto.
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

(** The dice-roll rule, derivable for every [k]. *)
Theorem HKRoll k eta : pfree c eta ->
  hoare_derivable (kroll_pformula k eta) (roll k) eta.
Proof.
  intros Hfree. apply loop_free_complete; [apply roll_loop_free|].
  intros ps Hps Hpre. apply (kroll_pformula_correct k eta ps Hps Hfree). exact Hpre.
Qed.

(** * Evaluating the roll sum with a symbolic bound *)

Fixpoint tdfree (t : Term) : Prop :=
  match t with
  | TProgVar y => y <> x
  | TOp _ t1 t2 => tdfree t1 /\ tdfree t2
  | _ => True
  end.

Fixpoint cdfree (g : CFormula) : Prop :=
  match g with
  | FRel _ t1 t2 => tdfree t1 /\ tdfree t2
  | FImpl g1 g2 => cdfree g1 /\ cdfree g2
  | _ => True
  end.

Fixpoint pdfree_term (p : Pterm) : Prop :=
  match p with
  | PProb g => cdfree g
  | PAdd p1 p2 | PMul p1 p2 => pdfree_term p1 /\ pdfree_term p2
  | _ => True
  end.

Fixpoint pdfree (eta : PFormula) : Prop :=
  match eta with
  | PFLe p1 p2 => pdfree_term p1 /\ pdfree_term p2
  | PFFalse => True
  | PFImpl e1 e2 => pdfree e1 /\ pdfree e2
  end.

Lemma subst_dom_term_dfree t u : tdfree t -> subst_dom_term x u t = t.
Proof.
  induction t as [y|y|k0|o t1 IH1 t2 IH2]; cbn; try reflexivity.
  - intros Hy. destruct (dom_program_var_eq_dec y x); [contradiction|reflexivity].
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma subst_dom_cformula_dfree g u : cdfree g -> subst_dom_cformula x u g = g.
Proof.
  induction g as [b|b|r0 t1 t2| |g1 IH1 g2 IH2]; cbn; try reflexivity.
  - intros [H1 H2]; rewrite !subst_dom_term_dfree by assumption; reflexivity.
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma subst_dom_pformula_dfree eta u : pdfree eta -> subst_dom_pformula x u eta = eta.
Proof.
  assert (Ht : forall p, pdfree_term p -> subst_dom_pterm x u p = p).
  { induction p as [y|r0|g|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn; try reflexivity.
    - intros Hg; rewrite subst_dom_cformula_dfree by exact Hg; reflexivity.
    - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
    - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity. }
  induction eta as [p1 p2| |e1 IH1 e2 IH2]; cbn; try reflexivity.
  - intros [H1 H2]; rewrite !Ht by assumption; reflexivity.
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma sumn_const (a : R) m : sumn (fun _ => a) m = INR m * a.
Proof.
  induction m as [|m IH]; cbn [sumn]; [cbn; lra|].
  rewrite IH, S_INR. lra.
Qed.

Lemma sumn_zero m : sumn (fun _ => 0) m = 0.
Proof. rewrite sumn_const; lra. Qed.

Lemma sumn_indicator (a : R) l m : (l < m)%nat ->
  sumn (fun i => if Nat.eqb i l then a else 0) m = a.
Proof.
  revert l; induction m as [|m IH]; intros l Hl; [lia|].
  cbn [sumn]. destruct l as [|l].
  - cbn [Nat.eqb]. erewrite sumn_ext; [rewrite sumn_zero; lra|].
    intros i _; reflexivity.
  - cbn [Nat.eqb]. rewrite (IH l) by lia. lra.
Qed.

(** If [g] does not mention [x], rolling [x] leaves [Pr(g)] unchanged. *)
Lemma roll_sum_dfree k g ps : cdfree g ->
  pterm_eval (roll_sum k g (S k) O) ps = Pr[ps] g.
Proof.
  intros Hg. rewrite roll_sum_eval.
  erewrite sumn_ext;
    [|intros i _; unfold gx; rewrite subst_dom_cformula_dfree by exact Hg; reflexivity].
  rewrite sumn_const. pose proof (pos_INR k). rewrite S_INR. field. lra.
Qed.

(** If [g[x := i]] is [phi /\ i = l] with [l <= k], rolling [x] scales
    [Pr(phi)] by [1/(k+1)]. *)
Lemma roll_sum_point k g phi l ps :
  (forall v i, satisfies v (gx g i) <-> satisfies v phi /\ i = l) -> (l <= k)%nat ->
  pterm_eval (roll_sum k g (S k) O) ps = / INR (S k) * Pr[ps] phi.
Proof.
  intros Hg Hl. rewrite roll_sum_eval.
  erewrite sumn_ext.
  2:{ intros i _. cbn [Nat.add].
      replace (Pr[ps] (gx g i)) with (if Nat.eqb i l then Pr[ps] phi else 0).
      - reflexivity.
      - destruct (Nat.eqb i l) eqn:E.
        + apply PeanoNat.Nat.eqb_eq in E; subst. apply Pr_ext; intro v.
          rewrite Hg; tauto.
        + apply PeanoNat.Nat.eqb_neq in E. rewrite <- (Pr_false ps).
          apply Pr_ext; intro v; rewrite Hg; cbn; tauto. }
  rewrite <- sumn_scale. rewrite sumn_indicator by lia. reflexivity.
Qed.

Lemma kroll_pterm_dfree k p ps : pdfree_term p ->
  pterm_eval (kroll_pterm k p) ps = pterm_eval p ps.
Proof.
  induction p as [y|r0|g|p1 IH1 p2 IH2|p1 IH1 p2 IH2]; cbn [kroll_pterm pdfree_term];
    try reflexivity.
  - intros Hg. rewrite roll_sum_dfree by exact Hg. reflexivity.
  - intros [H1 H2]; cbn [pterm_eval]; rewrite IH1, IH2 by assumption; reflexivity.
  - intros [H1 H2]; cbn [pterm_eval]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

Lemma kroll_pformula_dfree k eta ps : pdfree eta ->
  psatisfies ps (kroll_pformula k eta) <-> psatisfies ps eta.
Proof.
  induction eta as [p1 p2| |e1 IH1 e2 IH2]; cbn [kroll_pformula pdfree psatisfies].
  - intros [H1 H2]; rewrite !kroll_pterm_dfree by assumption; reflexivity.
  - tauto.
  - intros [H1 H2]; rewrite IH1, IH2 by assumption; reflexivity.
Qed.

(** * Frame rules *)

(** Rolling a variable the assertion does not mention preserves it. *)
Theorem HKRollFrame k eta : pfree c eta -> pdfree eta ->
  hoare_derivable eta (roll k) eta.
Proof.
  intros Hc Hx. eapply HConseqLeft; [|apply (HKRoll k eta Hc)].
  intros ps _ H. apply kroll_pformula_dfree; assumption.
Qed.

End Roll.

(** Assigning a variable the assertion does not mention preserves it. *)
Theorem HAssignFrame x t eta : pdfree x eta -> hoare_derivable eta (CDomAssign x t) eta.
Proof.
  intros Hx. pose proof (HDomAssign eta x t) as H.
  rewrite (subst_dom_pformula_dfree x eta t Hx) in H. exact H.
Qed.
