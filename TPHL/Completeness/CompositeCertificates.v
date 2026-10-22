(** Certificates for sequencing and conditionals, for arbitrary certified
    components (loops included).  Adapted from CPHL's
    Completeness/SequentialCertificates.v and ConditionalCertificates.v. *)
From Stdlib Require Import List Reals Lra.
Require Import PHL.
Require Import Soundness.AssertionFacts Soundness.TransformerAssertions
  Soundness.StructuralRules Soundness.SplitRules Soundness.CommandFacts.
Require Import Completeness.Interface Completeness.Freshness
  Completeness.StructuralRules Completeness.WeakestPreterm.
Import ListNotations.

Section CompositeCertificates.
Context {D : Domain}.
Local Notation Pterm := (Pterm D).

Definition seq_transformer (C1 : Cmd D) (T1 T2 : CFormula D -> Pterm) gamma :=
  wpt C1 T1 (T2 gamma).

Theorem seq_certificate C1 C2 T1 T2 :
  certificate C1 T1 -> certificate C2 T2 ->
  certificate (CSeq C1 C2) (seq_transformer C1 T1 T2).
Proof.
  intros H1 H2; constructor.
  - intros gamma y; unfold seq_transformer.
    rewrite (wpt_occurs C1 T1 (certificate_no_prob_vars _ _ H1)).
    apply (certificate_no_prob_vars _ _ H2).
  - intros ps gamma Hps; unfold seq_transformer.
    rewrite (wpt_correct C1 T1 (certificate_correct _ _ H1) (T2 gamma) ps Hps).
    rewrite (certificate_correct _ _ H2 _ gamma (run_admissible C1 Hps)).
    symmetry. exact (pterm_eval_same_masses _ _ (PProb gamma) (run_seq_same C1 C2 Hps)).
  - intros gamma y; unfold seq_transformer.
    eapply HSeq with (eta2 := p_eq (PVar y) (T2 gamma)).
    + apply wpt_transfer; [exact H1 | apply (certificate_no_prob_vars _ _ H2)].
    + apply (certificate_derivable _ _ H2).
Qed.

Definition if_transformer (beta : CFormula D) (T1 T2 : CFormula D -> Pterm) gamma :=
  PAdd (condition_pterm (T1 gamma) beta) (condition_pterm (T2 gamma) (c_not beta)).

Lemma condition_pterm_occurs (p : Pterm) beta y :
  prob_logic_var_occurs_pterm y (condition_pterm p beta) <->
  prob_logic_var_occurs_pterm y p.
Proof.
  induction p; cbn [condition_pterm prob_logic_var_occurs_pterm]; tauto.
Qed.

Theorem if_certificate beta C1 C2 T1 T2 :
  certificate C1 T1 -> certificate C2 T2 ->
  certificate (CIf beta C1 C2) (if_transformer beta T1 T2).
Proof.
  intros H1 H2; constructor.
  - intros gamma y; cbn [if_transformer prob_logic_var_occurs_pterm].
    rewrite !condition_pterm_occurs.
    pose proof (certificate_no_prob_vars _ _ H1 gamma y).
    pose proof (certificate_no_prob_vars _ _ H2 gamma y); tauto.
  - intros ps gamma Hps; cbn [if_transformer pterm_eval].
    rewrite !condition_pterm_correct.
    rewrite (certificate_correct _ _ H1 _ gamma (restrict_admissible beta Hps)).
    rewrite (certificate_correct _ _ H2 _ gamma (restrict_admissible (c_not beta) Hps)).
    cbn [pterm_eval]. symmetry. apply run_if_mass. exact Hps.
  - intros gamma y.
    set (a := condition_pterm (T1 gamma) beta).
    set (b := condition_pterm (T2 gamma) (c_not beta)).
    assert (Ha : forall z, ~ prob_logic_var_occurs_pterm z a).
    { intro z; unfold a; rewrite condition_pterm_occurs; apply (certificate_no_prob_vars _ _ H1). }
    assert (Hb : forall z, ~ prob_logic_var_occurs_pterm z b).
    { intro z; unfold b; rewrite condition_pterm_occurs; apply (certificate_no_prob_vars _ _ H2). }
    set (u := fresh_prob_logic_var [y]).
    set (v := fresh_prob_logic_var [u;y]).
    assert (Hu : ~ In u [y]) by apply fresh_prob_logic_var_not_in.
    assert (Hv : ~ In v [u;y]) by apply fresh_prob_logic_var_not_in.
    cbn in Hu, Hv.
    assert (Huy : y <> u) by tauto.
    assert (Hvy : y <> v) by tauto.
    assert (Huv : u <> v) by tauto.
    set (frame := p_eq (PVar y) (PAdd (PVar u) (PVar v)) : PFormula D).
    set (bindings := [(u,a);(v,b)]).
    assert (Hind : independent_bindings bindings).
    { split.
      - cbn [bindings map]; repeat constructor; cbn; intuition congruence.
      - intros z r w t Hz Ht; cbn [bindings] in Ht.
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Ha |].
        destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Hb | contradiction]. }
    assert (Hpost : forall z r, In (z,r) bindings ->
      ~ prob_logic_var_occurs_pformula z (p_eq (PVar y) (PProb gamma))).
    { intros z r Hz; cbn [bindings] in Hz.
      destruct Hz as [Hz | Hz]; [inversion Hz; subst z r |].
      - cbn; intuition congruence.
      - destruct Hz as [Hz | Hz]; [inversion Hz; subst z r | contradiction].
        cbn; intuition congruence. }
    assert (Hder : hoare_derivable (bindings_precondition bindings frame)
      (CIf beta C1 C2) (p_eq (PVar y) (PProb gamma))).
    { eapply derive_post with (post := p_and
        (p_eq (PAdd (PVar u) (PVar v)) (PProb gamma)) frame).
      - apply HAnd.
        + eapply derive_pre with (pre' := if_precondition
            (p_eq (PVar u) (T1 gamma)) (p_eq (PVar v) (T2 gamma)) beta).
          * intros ps Hps H; cbn [bindings bindings_precondition] in H.
            rewrite !psatisfies_and in H.
            unfold if_precondition; apply psatisfies_and; split.
            -- change (psatisfies ps (p_eq (PVar u) a)); tauto.
            -- change (psatisfies ps (p_eq (PVar v) b)); tauto.
          * apply derive_if_eq;
              [apply (certificate_derivable _ _ H1) | apply (certificate_derivable _ _ H2)].
        + eapply derive_pre with (pre' := frame).
          * intros ps Hps H; cbn [bindings bindings_precondition] in H.
            rewrite !psatisfies_and in H; tauto.
          * apply HFree; unfold frame; cbn; tauto.
      - intros ps Hps H; apply psatisfies_and in H; destruct H as [Hsum Hframe].
        apply psatisfies_eq in Hsum; unfold frame in Hframe; apply psatisfies_eq in Hframe.
        apply psatisfies_eq; cbn [pterm_eval] in *; congruence. }
    pose proof (derive_eliminate_bindings bindings frame _ _ Hind Hpost Hder) as Hresult.
    assert (Heq : substitute_bindings bindings frame = p_eq (PVar y) (PAdd a b)).
    { unfold bindings, frame; cbn [substitute_bindings subst_prob_pformula p_eq p_and p_not subst_prob_pterm].
      repeat match goal with
      | |- context [prob_logic_var_eq_dec ?z ?w] =>
          destruct (prob_logic_var_eq_dec z w); cbn [subst_prob_pterm]
      end; try congruence;
      rewrite (subst_prob_pterm_fresh v b a (Ha v)); reflexivity. }
    rewrite Heq in Hresult; exact Hresult.
Qed.

End CompositeCertificates.
