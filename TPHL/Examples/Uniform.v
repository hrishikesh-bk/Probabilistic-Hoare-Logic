(** Uniform sampling from fair coins.

    [uniform_exp k] builds [val] bit by bit: [k] times, toss [b] and set
    [val := #(2%nat) * val + b].  Starting from [val = 0] this gives the uniform
    distribution on [0, 2^k).  [uniform_k k] repeats it until [val < k],
    which gives the uniform distribution on [0, k). *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
Require Import PHL Examples.Lib Examples.PrAtoms.
Require Import Soundness.StateFacts Soundness.AssertionFacts Completeness.StructuralRules.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

(** * Local helpers *)

(** Embed a real-valued Coq term in a probabilistic formula. *)
Notation "'#(' x ')'" := (pconst x) (in custom tpf at level 0, x constr at level 200)
  : tphl_scope.

(** A formula probability that is already in canonical form. *)
Definition Pc (ps : Pstate) (g : CFormula) : R := Pr[ps] g.

(** Rewrite [Pr[ps] X] into [Pc ps G] for the first [G] in [Gs] equivalent
    to [X], or into [0] when [X] is unsatisfiable. *)
Ltac pcanon_one ps X Gs :=
  lazymatch Gs with
  | cons ?G ?rest =>
      first
        [ let E := fresh "E" in
          assert (E : Pr[ps] X = Pc ps G) by (unfold Pc; apply Pr_ext; cdecide);
          rewrite E in *; clear E
        | pcanon_one ps X rest ]
  | nil =>
      let E := fresh "E" in
      assert (E : Pr[ps] X = 0) by (rewrite <- (Pr_false ps); apply Pr_ext; cdecide);
      rewrite E in *; clear E
  end.

Ltac pcanon Gs :=
  repeat match goal with
  | |- context [Pr[?ps] ?X] => pcanon_one ps X Gs
  | H : context [Pr[?ps] ?X] |- _ => pcanon_one ps X Gs
  end.

Lemma Pc_nonneg ps g : 0 <= Pc ps g.
Proof. apply Pr_nonneg. Qed.

Module Uniform.

Notation b := (bool_program_var "b").
Notation val := (dom_program_var "val").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").

Definition body : Cmd :=
  <{ b toss 0.5; if b then val := #(2%nat) * val + #(1%nat) else val := #(2%nat) * val end }>.

Fixpoint uniform_exp (k : nat) : Cmd :=
  match k with
  | O => CSkip
  | S n => CSeq (uniform_exp n) body
  end.

Definition twok (k : nat) : R := 1 / 2 ^ k.

(** * One step: [Pr(val = k) = r] becomes [Pr(val = 2k) = Pr(val = 2k+1) = r/2]

    Each assignment by [HConseq] + [HDomAssign] ([asgn2k*]), the
    conditional by [HIfEq] ([ifthenpre*]) and [HConseq] ([intermediate*]),
    and the branch variables removed by [HInstantiate] ([eliminate_y*]). *)

Notation ifc :=
  (<{ if b then val := #(2%nat) * val + #(1%nat) else val := #(2%nat) * val end }>)
  (only parsing).

Theorem asgn2k_1 (k : nat) (r : R) :
  hoare_derivable {{ (prob (val = k)) = 0.5 * r /\ y1 = 0.5 * r }}
    <{ val := #(2%nat) * val }> {{ (prob (val = #((2 * k)%nat))) = y1 }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. pcanon [\{ val = k \}]. lra.
Qed.

Theorem asgn2k_0 (k : nat) (r : R) :
  hoare_derivable {{ (prob (val = k)) = 0.5 * r /\ y1 = 0 }}
    <{ val := #(2%nat) * val }> {{ (prob (val = #((2 * k + 1)%nat))) = y1 }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. pcanon [\{ val = k \}]. lra.
Qed.

Theorem asgn2k1_1 (k : nat) (r : R) :
  hoare_derivable {{ (prob (val = k)) = 0.5 * r /\ y2 = 0.5 * r }}
    <{ val := #(2%nat) * val + #(1%nat) }> {{ (prob (val = #((2 * k + 1)%nat))) = y2 }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. pcanon [\{ val = k \}]. lra.
Qed.

Theorem asgn2k1_0 (k : nat) (r : R) :
  hoare_derivable {{ (prob (val = k)) = 0.5 * r /\ y2 = 0 }}
    <{ val := #(2%nat) * val + #(1%nat) }> {{ (prob (val = #((2 * k)%nat))) = y2 }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. pcanon [\{ val = k \}]. lra.
Qed.

Theorem ifthenpre1 (k : nat) (r : R) :
  hoare_derivable
    (if_precondition {{ (prob (val = k)) = 0.5 * r /\ y2 = 0.5 * r }}
                     {{ (prob (val = k)) = 0.5 * r /\ y1 = 0 }} (FProgBool b))
    ifc {{ y2 + y1 = (prob (val = #((2 * k + 1)%nat))) }}.
Proof.
  apply HIfEq.
  - eapply HConseqRight; [|apply asgn2k1_1]. ptrans; pvalid. lra.
  - eapply HConseqRight; [|apply asgn2k_0]. ptrans; pvalid. lra.
Qed.

Theorem ifthenpre0 (k : nat) (r : R) :
  hoare_derivable
    (if_precondition {{ (prob (val = k)) = 0.5 * r /\ y2 = 0 }}
                     {{ (prob (val = k)) = 0.5 * r /\ y1 = 0.5 * r }} (FProgBool b))
    ifc {{ y2 + y1 = (prob (val = #((2 * k)%nat))) }}.
Proof.
  apply HIfEq.
  - eapply HConseqRight; [|apply asgn2k1_0]. ptrans; pvalid. lra.
  - eapply HConseqRight; [|apply asgn2k_1]. ptrans; pvalid. lra.
Qed.

Theorem intermediate0 (k : nat) (r : R) :
  hoare_derivable
    {{ (((prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r) /\ y2 = 0)
       /\ y1 = 0.5 * r }}
    ifc {{ y2 + y1 = (prob (val = #((2 * k)%nat))) }}.
Proof.
  eapply HConseqLeft; [|apply ifthenpre0].
  ptrans; pvalid. pcanon [\{ val = k /\ b \}; \{ val = k /\ ~ b \}]. split_hyps. lra.
Qed.

Theorem intermediate1 (k : nat) (r : R) :
  hoare_derivable
    {{ (((prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r) /\ y2 = 0.5 * r)
       /\ y1 = 0 }}
    ifc {{ y2 + y1 = (prob (val = #((2 * k + 1)%nat))) }}.
Proof.
  eapply HConseqLeft; [|apply ifthenpre1].
  ptrans; pvalid. pcanon [\{ val = k /\ b \}; \{ val = k /\ ~ b \}]. split_hyps. lra.
Qed.

Theorem eliminate_y1_0 (k : nat) (r : R) :
  hoare_derivable
    {{ ((prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r) /\ y2 = 0 }}
    ifc {{ y2 + 0.5 * r = (prob (val = #((2 * k)%nat))) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y1 (0.5 * r) _ _ _ (intermediate0 k r))|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem eliminate_y2_0 (k : nat) (r : R) :
  hoare_derivable
    {{ (prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r }}
    ifc {{ 0.5 * r = (prob (val = #((2 * k)%nat))) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y2 0 _ _ _ (eliminate_y1_0 k r))|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem eliminate_y1_1 (k : nat) (r : R) :
  hoare_derivable
    {{ ((prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r) /\ y2 = 0.5 * r }}
    ifc {{ y2 + 0 = (prob (val = #((2 * k + 1)%nat))) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y1 0 _ _ _ (intermediate1 k r))|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem eliminate_y2_1 (k : nat) (r : R) :
  hoare_derivable
    {{ (prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r }}
    ifc {{ 0.5 * r = (prob (val = #((2 * k + 1)%nat))) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y2 (0.5 * r) _ _ _ (eliminate_y1_1 k r))|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem tossb (k : nat) (r : R) :
  hoare_derivable {{ (prob (val = k)) = r }} <{ b toss 0.5 }>
    {{ (prob (val = k /\ b)) = 0.5 * r /\ (prob (val = k /\ ~ b)) = 0.5 * r }}.
Proof.
  eapply HConseqLeft; [|apply HBoolToss; unfold coin_probability_valid; lra].
  ptrans; pvalid. pcanon [\{ val = k \}]. lra.
Qed.

Theorem body1 (j : nat) (r : R) :
  hoare_derivable {{ (prob (val = j)) = r }} body
    {{ 0.5 * r = (prob (val = #((2 * j + 1)%nat))) }}.
Proof.
  apply HSeq with (eta2 := {{ (prob (val = j /\ b)) = 0.5 * r /\
                              (prob (val = j /\ ~ b)) = 0.5 * r }}).
  - apply tossb.
  - apply eliminate_y2_1.
Qed.

Theorem body2 (j : nat) (r : R) :
  hoare_derivable {{ (prob (val = j)) = r }} body
    {{ 0.5 * r = (prob (val = #((2 * j)%nat))) }}.
Proof.
  apply HSeq with (eta2 := {{ (prob (val = j /\ b)) = 0.5 * r /\
                              (prob (val = j /\ ~ b)) = 0.5 * r }}).
  - apply tossb.
  - apply eliminate_y2_0.
Qed.

(** * Total mass is preserved (same pattern, [gamma = true]) *)

Theorem asgn_t0 :
  hoare_derivable {{ (prob true) = 0.5 /\ y2 = 0.5 }} <{ val := #(2%nat) * val }>
    {{ y2 = (prob true) }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. split_hyps. pcanon [\{ true \}]. unfold Pc in *. lra.
Qed.

Theorem asgn_t1 :
  hoare_derivable {{ (prob true) = 0.5 /\ y1 = 0.5 }} <{ val := #(2%nat) * val + #(1%nat) }>
    {{ y1 = (prob true) }}.
Proof.
  eapply HConseqLeft; [|apply HDomAssign].
  ptrans; pvalid. split_hyps. pcanon [\{ true \}]. unfold Pc in *. lra.
Qed.

Theorem ifthen_t :
  hoare_derivable
    {{ (((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) /\ y1 = 0.5) /\ y2 = 0.5 }}
    ifc {{ y1 + y2 = (prob true) }}.
Proof.
  eapply HConseqLeft with
    (pre' := if_precondition {{ (prob true) = 0.5 /\ y1 = 0.5 }}
                             {{ (prob true) = 0.5 /\ y2 = 0.5 }} (FProgBool b)).
  - ptrans; pvalid. pcanon [\{ true /\ b \}; \{ true /\ ~ b \}]. split_hyps. lra.
  - apply HIfEq; [apply asgn_t1 | apply asgn_t0].
Qed.

Theorem elimy2_t :
  hoare_derivable
    {{ ((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) /\ y1 = 0.5 }}
    ifc {{ y1 + 0.5 = (prob true) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y2 0.5 _ _ _ ifthen_t)|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem elimy1_t :
  hoare_derivable {{ (prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5 }}
    ifc {{ 1 = (prob true) }}.
Proof.
  eapply HConseq; [|apply (HInstantiate y1 0.5 _ _ _ elimy2_t)|].
  - ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem tosst :
  hoare_derivable {{ (prob true) = 1 }} <{ b toss 0.5 }>
    {{ (prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5 }}.
Proof.
  eapply HConseqLeft; [|apply HBoolToss; unfold coin_probability_valid; lra].
  ptrans; pvalid. pcanon [\{ true \}]. lra.
Qed.

Theorem bodyt : hoare_derivable {{ (prob true) = 1 }} body {{ (prob true) = 1 }}.
Proof.
  apply HSeq with (eta2 := {{ (prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5 }}).
  - apply tosst.
  - apply HConseqRight with (post := {{ 1 = (prob true) }});
    [ptrans; pvalid; pcanon [\{ true \}]; unfold Pc in *; lra|].
    apply elimy1_t.
Qed.

Theorem uniform_exp_true k :
  hoare_derivable {{ (prob true) = 1 }} (uniform_exp k) {{ (prob true) = 1 }}.
Proof.
  induction k as [|k IH]; cbn [uniform_exp].
  - apply HSkip.
  - apply HSeq with (eta2 := {{ (prob true) = 1 }}); [exact IH | apply bodyt].
Qed.

(** * [uniform_exp k] is uniform on [0, 2^k) *)

Lemma twok_S k : 0.5 * twok k = twok (S k).
Proof.
  unfold twok. cbn [pow]. replace 0.5 with (/ 2) by lra.
  assert (H : 2 ^ k <> 0) by (apply pow_nonzero; lra). field. exact H.
Qed.

Lemma two_pow_ne k : 2 ^ k <> 0.
Proof. apply pow_nonzero; lra. Qed.

Lemma k_le_2k k : (k <= 2 ^ k)%nat.
Proof. pose proof (Nat.pow_gt_lin_r 2 k ltac:(lia)); lia. Qed.

Lemma Pr_compl (ps : Pstate) (Hps : pstate_admissible ps) (g : CFormula) :
  Pr[ps] (c_not g) = Pr[ps] c_true - Pr[ps] g.
Proof.
  rewrite (Pr_split ps Hps c_true g).
  rewrite (Pr_ext ps (c_and c_true g) g), (Pr_ext ps (c_and c_true (c_not g)) (c_not g))
    by (intros v; rewrite satisfies_and; pose proof (satisfies_true v); tauto).
  lra.
Qed.

Lemma div_nonneg a c : 0 <= a -> 0 < c -> 0 <= a / c.
Proof. intros Ha Hc. unfold Rdiv. apply Rmult_le_pos; [lra|]. left; apply Rinv_0_lt_compat; lra. Qed.

Lemma div_pos a c : 0 < a -> 0 < c -> 0 < a / c.
Proof. intros Ha Hc. unfold Rdiv. apply Rmult_lt_0_compat; [lra|]. apply Rinv_0_lt_compat; lra. Qed.

Lemma k_pos k k1 : (k1 < k)%nat -> 0 < INR k.
Proof. intros H. apply lt_0_INR. lia. Qed.

Lemma ratio_bounds k : 0 <= INR k / 2 ^ k <= 1.
Proof.
  pose proof (pos_INR k). pose proof (pow_lt 2 k ltac:(lra)).
  pose proof (le_INR _ _ (k_le_2k k)) as Hle. rewrite pow_INR in Hle.
  replace (INR 2) with 2 in Hle by (simpl; lra).
  split; [apply div_nonneg; lra|].
  apply (Rmult_le_reg_r (2 ^ k)); [lra|]. field_simplify; lra.
Qed.

(** Intermediate postconditions of [unif]. *)
Definition post (k k1 : nat) : PFormula := {{ (prob (val = k1)) = #(twok k) }}.
Definition post1 (k k1 : nat) : PFormula := {{ (prob (val < k1)) = #(INR k1 / 2 ^ k) }}.

Theorem unif (k k1 : nat) : (k1 < 2 ^ k)%nat ->
  hoare_derivable {{ (prob (val = #(0%nat))) = 1 }} (uniform_exp k)
    {{ (prob (val = k1)) = #(twok k) }}.
Proof.
  revert k1; induction k as [|k IH]; intros k1 Hk1.
  - cbn in Hk1. assert (k1 = 0)%nat by lia; subst.
    cbn [uniform_exp]. apply HConseqRight with (post := {{ (prob (val = #(0%nat))) = 1 }}).
    + ptrans; pvalid. unfold twok. cbn [pow]. lra.
    + apply HSkip.
  - cbn [uniform_exp].
    destruct (Nat.Even_or_Odd k1) as [[j Hj]|[j Hj]]; subst k1.
    + apply HSeq with (eta2 := post k j); [apply IH; rewrite Nat.pow_succ_r' in Hk1; lia|].
      apply HConseqRight with (post := {{ (prob (val = #((2 * j)%nat))) = #(0.5 * twok k) }}).
      { ptrans; pvalid. rewrite <- twok_S. lra. }
      eapply HConseq; [|apply (body2 j (twok k))|].
      * unfold post. ptrans; pvalid. lra.
      * ptrans; pvalid. lra.
    + apply HSeq with (eta2 := post k j); [apply IH; rewrite Nat.pow_succ_r' in Hk1; lia|].
      apply HConseqRight with (post := {{ (prob (val = #((2 * j + 1)%nat))) = #(0.5 * twok k) }}).
      { ptrans; pvalid. rewrite <- twok_S. lra. }
      eapply HConseq; [|apply (body1 j (twok k))|].
      * unfold post. ptrans; pvalid. lra.
      * ptrans; pvalid. lra.
Qed.

Theorem unif_sum (k k1 : nat) : (k1 <= 2 ^ k)%nat ->
  hoare_derivable {{ (prob (val = #(0%nat))) = 1 }} (uniform_exp k)
    {{ (prob (val < k1)) = #(INR k1 / 2 ^ k) }}.
Proof.
  induction k1 as [|k1 IH]; intros Hk1.
  - apply HConseqRight with (post := post k 0).
    + unfold post. ptrans; pvalid. pcanon (@nil CFormula). cbn [INR]. lra.
    + apply unif. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia.
  - apply HConseqRight with (post := p_and (post1 k k1) (post k k1)).
    + unfold post, post1. ptrans; pvalid. pcanon [\{ val < k1 \}; \{ val = k1 \}].
      rewrite (Pr_ext ps _ (c_or \{ val < k1 \} \{ val = k1 \})) by cdecide.
      rewrite (Pr_disjoint ps Hps) by cdecide.
      unfold Pc, twok in *. rewrite S_INR.
      assert (H2 : 2 ^ k <> 0) by (apply pow_nonzero; lra).
      replace ((INR k1 + 1) / 2 ^ k) with (INR k1 / 2 ^ k + 1 / 2 ^ k) by (field; exact H2).
      lra.
    + apply HAnd; [apply IH; lia | apply unif; lia].
Qed.

Theorem unif_full k :
  hoare_derivable {{ (prob (val = #(0%nat))) = 1 }} (uniform_exp k)
    {{ (prob (val < #((2 ^ k)%nat))) = 1 }}.
Proof.
  apply HConseqRight with (post := post1 k (2 ^ k)).
  - unfold post1. ptrans; pvalid. rewrite H, pow_INR.
    replace (INR 2) with 2 by (simpl; lra). field. apply two_pow_ne.
  - apply unif_sum. lia.
Qed.

Theorem unif_empty k :
  hoare_derivable {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }} (uniform_exp k)
    {{ (prob (#((2 ^ k)%nat) <= val)) = 0 }}.
Proof.
  apply HConseqRight with (post := {{ (prob (val < #((2 ^ k)%nat))) = 1 /\ (prob true) = 1 }}).
  - ptrans; pvalid. split_hyps.
    rewrite (Pr_ext ps _ (c_not \{ val < #((2 ^ k)%nat) \})) by cdecide.
    rewrite (Pr_compl ps Hps). pcanon [\{ val < #((2 ^ k)%nat) \}; \{ true \}]. lra.
  - apply HAnd.
    + apply HConseqLeft with (pre' := {{ (prob (val = #(0%nat))) = 1 }});
        [ptrans; pvalid; split_hyps; lra | apply unif_full].
    + apply HConseqLeft with (pre' := {{ (prob true) = 1 }});
        [ptrans; pvalid; split_hyps; lra | apply uniform_exp_true].
Qed.

Theorem unif_ge (k k1 : nat) : (k1 <= 2 ^ k)%nat ->
  hoare_derivable {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }} (uniform_exp k)
    {{ (prob (k1 <= val)) = #(1 - INR k1 / 2 ^ k) }}.
Proof.
  intros Hk1.
  apply HConseqRight with
    (post := {{ (prob (val < k1)) = #(INR k1 / 2 ^ k) /\
                ((prob (val < #((2 ^ k)%nat))) = 1 /\ (prob (#((2 ^ k)%nat) <= val)) = 0) }}).
  - ptrans; pvalid. split_hyps.
    rewrite (Pr_ext ps _ (c_not \{ val < k1 \})) by cdecide.
    rewrite (Pr_compl ps Hps).
    pose proof (Pr_split ps Hps c_true \{ val < #((2 ^ k)%nat) \}).
    pcanon [\{ val < k1 \}; \{ val < #((2 ^ k)%nat) \}; \{ #((2 ^ k)%nat) <= val \}; \{ true \}].
    unfold Pc in *. lra.
  - apply HAnd.
    + apply HConseqLeft with (pre' := {{ (prob (val = #(0%nat))) = 1 }});
        [ptrans; pvalid; split_hyps; lra | apply unif_sum; exact Hk1].
    + apply HAnd.
      * apply HConseqLeft with (pre' := {{ (prob (val = #(0%nat))) = 1 }});
          [ptrans; pvalid; split_hyps; lra | apply unif_full].
      * apply unif_empty.
Qed.

(** * Rejection sampling: uniform on [0, k) *)

Definition body_unif_k (k : nat) : Cmd := CSeq (CDomAssign val (tnat 0)) (uniform_exp k).
Definition guard (k : nat) : CFormula := \{ k <= val \}.
Definition uniform_k (k : nat) : Cmd := CWhile (guard k) (body_unif_k k).

Theorem body_unif_k_t k :
  hoare_derivable {{ (prob true) = 1 }} (body_unif_k k) {{ (prob true) = 1 }}.
Proof.
  apply HSeq with (eta2 := {{ (prob true) = 1 }}).
  - eapply HConseq;
      [|apply (HDomAssign {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }})|].
    + ptrans; pvalid. pcanon [\{ true \}]. unfold Pc in *. split; lra.
    + ptrans; pvalid. split_hyps. lra.
  - apply uniform_exp_true.
Qed.

(** The body premises of the while rules.  Their
    precondition is the rule's "all mass in the region" form. *)
Definition post_body_t (k : nat) : PFormula :=
  {{ (prob (k <= val)) <= #(1 - INR k / 2 ^ k) /\
     (prob (~ (k <= val) /\ true)) <= #(INR k / 2 ^ k) }}.
Definition post_body_LB_t (k : nat) : PFormula :=
  {{ #(1 - INR k / 2 ^ k) <= (prob (k <= val)) /\
     #(INR k / 2 ^ k) <= (prob (~ (k <= val) /\ true)) }}.
Definition post_body (k k1 : nat) : PFormula :=
  {{ (prob (k <= val)) <= #(1 - INR k / 2 ^ k) /\
     (prob (~ (k <= val) /\ val = k1)) <= #(twok k) }}.
Definition post_body_LB (k k1 : nat) : PFormula :=
  {{ #(1 - INR k / 2 ^ k) <= (prob (k <= val)) /\
     #(twok k) <= (prob (~ (k <= val) /\ val = k1)) }}.

(** Entering the body: [val := 0] with all mass in the guard. *)
Ltac reset_side k :=
  unfold guard, p_concentrated_unit, p_almost_sure; ptrans; pvalid; split_hyps;
  pcanon [\{ true \}; \{ k <= val \}]; unfold Pc in *; split; lra.

Theorem body_unif_t_prop (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable (p_concentrated_unit (guard k)) (body_unif_k k) (post_body_t k).
Proof.
  intros Hk1. apply HAnd.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + apply HConseqRight with (post := {{ (prob (k <= val)) = #(1 - INR k / 2 ^ k) }}).
      * ptrans; pvalid. lra.
      * apply unif_ge, k_le_2k.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + eapply HConseq; [|apply (unif_sum k k (k_le_2k k))|].
      * ptrans; pvalid. split_hyps. lra.
      * ptrans; pvalid. pcanon [\{ val < k \}]. unfold Pc in *. lra.
Qed.

Theorem body_unif_prop_LB_t (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable (p_concentrated_unit (guard k)) (body_unif_k k) (post_body_LB_t k).
Proof.
  intros Hk1. apply HAnd.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + apply HConseqRight with (post := {{ (prob (k <= val)) = #(1 - INR k / 2 ^ k) }}).
      * ptrans; pvalid. lra.
      * apply unif_ge, k_le_2k.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + eapply HConseq; [|apply (unif_sum k k (k_le_2k k))|].
      * ptrans; pvalid. split_hyps. lra.
      * ptrans; pvalid. pcanon [\{ val < k \}]. unfold Pc in *. lra.
Qed.

Theorem body_unif_prop (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable (p_concentrated_unit (guard k)) (body_unif_k k) (post_body k k1).
Proof.
  intros Hk1. apply HAnd.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + apply HConseqRight with (post := {{ (prob (k <= val)) = #(1 - INR k / 2 ^ k) }}).
      * ptrans; pvalid. lra.
      * apply unif_ge, k_le_2k.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + eapply HConseq; [|apply (unif k k1); pose proof (k_le_2k k); lia|].
      * ptrans; pvalid. split_hyps. lra.
      * unfold post. ptrans; pvalid.
        pose proof (Pr_mono ps Hps \{ ~ (k <= val) /\ val = k1 \} \{ val = k1 \} ltac:(cdecide)).
        pcanon [\{ ~ (k <= val) /\ val = k1 \}; \{ val = k1 \}]. unfold Pc in *. lra.
Qed.

Theorem body_unif_prop_LB (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable (p_concentrated_unit (guard k)) (body_unif_k k) (post_body_LB k k1).
Proof.
  intros Hk1. apply HAnd.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + apply HConseqRight with (post := {{ (prob (k <= val)) = #(1 - INR k / 2 ^ k) }}).
      * ptrans; pvalid. lra.
      * apply unif_ge, k_le_2k.
  - apply HSeq with (eta2 := {{ (prob (val = #(0%nat))) = 1 /\ (prob true) = 1 }}).
    + eapply HConseqLeft; [|apply HDomAssign]. reset_side k.
    + eapply HConseq; [|apply (unif k k1); pose proof (k_le_2k k); lia|].
      * ptrans; pvalid. split_hyps. lra.
      * unfold post. ptrans; pvalid.
        pcanon [\{ val = k1 \}]. unfold Pc in *. lra.
Qed.

(** ** Termination ([gamma = tt]) *)

Theorem uniform_k_UB_inter_t (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ box (#(guard k) /\ #(guard k)) /\ (prob true) <= y1 }} (uniform_k k)
    {{ (prob true) <= 1 * y1 }}.
Proof.
  intros Hk1. pose proof (ratio_bounds k).
  apply (HWhileUpper 1 0 (guard k) c_true (body_unif_k k) (fun _ => guard k)
           (fun _ => 1) (fun _ => INR k / 2 ^ k) (fun _ _ => 1 - INR k / 2 ^ k) y1).
  - lia.
  - while_side. unfold guard. cdecide.
  - below_cases. eapply HConseqRight; [|apply (body_unif_t_prop k k1 Hk1)].
    unfold post_body_t, guard. ptrans; pvalid. split_hyps.
    pcanon [\{ k <= val \}; \{ ~ (k <= val) \}]. unfold Pc in *. split; [split; [tauto|lra]|lra].
  - while_side. below_cases. split; lra.
Qed.

Theorem uniform_k_LB_inter_t (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ box (#(guard k) /\ #(guard k)) /\ y1 <= (prob true) }} (uniform_k k)
    {{ 1 * y1 <= (prob true) }}.
Proof.
  intros Hk1. pose proof (ratio_bounds k). pose proof (k_pos k k1 Hk1).
  pose proof (pow_lt 2 k ltac:(lra)).
  apply (HWhileLower 1 0 (guard k) c_true (body_unif_k k) (fun _ => guard k)
           (fun _ => 1) (fun _ => INR k / 2 ^ k) (fun _ _ => 1 - INR k / 2 ^ k) y1).
  - lia.
  - while_side. below_cases. unfold guard. cdecide.
  - while_side. intros i j Hi Hj. lia.
  - while_side. below_cases. left. apply div_pos; lra.
  - below_cases. eapply HConseqRight; [|apply (body_unif_prop_LB_t k k1 Hk1)].
    unfold post_body_LB_t, guard. ptrans; pvalid. split_hyps.
    pcanon [\{ k <= val \}; \{ ~ (k <= val) \}]. unfold Pc in *. split; [split; [tauto|lra]|lra].
  - while_side. below_cases. split; lra.
Qed.

Theorem uniform_k_inter_t (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ (prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}
    (uniform_k k) {{ 1 * y1 = (prob true) }}.
Proof.
  intros Hk1.
  apply HConseqLeft with
    (pre' := {{ (prob (#(guard k) /\ #(guard k))) = y1 /\
                (prob (#(guard k) /\ #(guard k))) = (prob true) }}).
  { unfold guard. ptrans; pvalid. pcanon [\{ k <= val \}; \{ true \}]. split_hyps. split; lra. }
  apply HConseqRight with (post := {{ (prob true) <= 1 * y1 /\ 1 * y1 <= (prob true) }}).
  { ptrans; pvalid. split_hyps. lra. }
  apply HAnd.
  - apply HConseqLeft with (pre' := {{ box (#(guard k) /\ #(guard k)) /\ (prob true) <= y1 }}).
    + ptrans; pvalid. split_hyps. split; lra.
    + apply (uniform_k_UB_inter_t k k1 Hk1).
  - apply HConseqLeft with (pre' := {{ box (#(guard k) /\ #(guard k)) /\ y1 <= (prob true) }}).
    + ptrans; pvalid. split_hyps. split; lra.
    + apply (uniform_k_LB_inter_t k k1 Hk1).
Qed.

(** Starting at [val = k], the loop terminates with probability 1. *)
Theorem uniform_t (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ (prob (val = k)) = 1 /\ (prob (val = k)) = (prob true) }}
    (uniform_k k) {{ 1 = (prob true) }}.
Proof.
  intros Hk1.
  apply HConseqLeft with (pre' := {{ (prob (k <= val)) = 1 /\ (prob (k <= val)) = (prob true) }}).
  { ptrans; pvalid. split_hyps.
    pose proof (Pr_mono ps Hps \{ val = k \} \{ k <= val \} ltac:(cdecide)).
    pose proof (Pr_le_true ps Hps \{ k <= val \}).
    pcanon [\{ val = k \}; \{ k <= val \}; \{ true \}]. unfold Pc in *.
    split; lra. }
  assert (Hy : hoare_derivable
                 {{ ((prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true)) /\ y1 = 1 }}
                 (uniform_k k) {{ 1 * y1 = (prob true) }}).
  { apply HConseqLeft with (pre' := {{ (prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}).
    - ptrans; pvalid. split_hyps. split; lra.
    - apply (uniform_k_inter_t k k1 Hk1). }
  eapply HConseq; [|apply (HInstantiate y1 1 _ _ _ Hy)|].
  - ptrans; pvalid. split_hyps. split; [split|]; lra.
  - ptrans; pvalid. lra.
Qed.

(** ** Uniformity ([gamma = (val = k1)]) *)

Theorem uniform_k_UB_inter (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ box (#(guard k) /\ #(guard k)) /\ (prob true) <= y1 }} (uniform_k k)
    {{ (prob (val = k1)) <= #(1 / INR k) * y1 }}.
Proof.
  intros Hk1. pose proof (ratio_bounds k). pose proof (k_pos k k1 Hk1).
  pose proof (pow_lt 2 k ltac:(lra)).
  apply (HWhileUpper 1 0 (guard k) \{ val = k1 \} (body_unif_k k) (fun _ => guard k)
           (fun _ => 1 / INR k) (fun _ => twok k) (fun _ _ => 1 - INR k / 2 ^ k) y1).
  - lia.
  - while_side. unfold guard. cdecide.
  - below_cases. eapply HConseqRight; [|apply (body_unif_prop k k1 Hk1)].
    unfold post_body, guard. ptrans; pvalid. split_hyps.
    pcanon [\{ k <= val \}; \{ ~ (k <= val) /\ val = k1 \}]. unfold Pc in *.
    split; [split; [tauto|lra]|lra].
  - while_side. below_cases. unfold twok.
    split; [right; field; lra|].
    split; [apply div_nonneg; lra|].
    assert (Hk1' : 1 <= INR k) by (change 1 with (INR 1); apply le_INR; lia).
    unfold Rdiv. rewrite Rmult_1_l. rewrite <- Rinv_1. apply Rinv_le_contravar; lra.
Qed.

Theorem uniform_k_LB_inter (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ box (#(guard k) /\ #(guard k)) /\ y1 <= (prob true) }} (uniform_k k)
    {{ #(1 / INR k) * y1 <= (prob (val = k1)) }}.
Proof.
  intros Hk1. pose proof (ratio_bounds k). pose proof (k_pos k k1 Hk1).
  pose proof (pow_lt 2 k ltac:(lra)).
  apply (HWhileLower 1 0 (guard k) \{ val = k1 \} (body_unif_k k) (fun _ => guard k)
           (fun _ => 1 / INR k) (fun _ => twok k) (fun _ _ => 1 - INR k / 2 ^ k) y1).
  - lia.
  - while_side. below_cases. unfold guard. cdecide.
  - while_side. intros i j Hi Hj. lia.
  - while_side. below_cases. left. unfold twok. apply div_pos; lra.
  - below_cases. eapply HConseqRight; [|apply (body_unif_prop_LB k k1 Hk1)].
    unfold post_body_LB, guard. ptrans; pvalid. split_hyps.
    pcanon [\{ k <= val \}; \{ ~ (k <= val) /\ val = k1 \}]. unfold Pc in *.
    split; [split; [tauto|lra]|lra].
  - while_side. below_cases. unfold twok.
    split; [right; field; lra|].
    split; [apply div_nonneg; lra|].
    assert (Hk1' : 1 <= INR k) by (change 1 with (INR 1); apply le_INR; lia).
    unfold Rdiv. rewrite Rmult_1_l. rewrite <- Rinv_1. apply Rinv_le_contravar; lra.
Qed.

Theorem uniform_k_inter (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ (prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}
    (uniform_k k) {{ #(1 / INR k) * y1 = (prob (val = k1)) }}.
Proof.
  intros Hk1.
  apply HConseqLeft with
    (pre' := {{ (prob (#(guard k) /\ #(guard k))) = y1 /\
                (prob (#(guard k) /\ #(guard k))) = (prob true) }}).
  { unfold guard. ptrans; pvalid. pcanon [\{ k <= val \}; \{ true \}]. split_hyps. split; lra. }
  apply HConseqRight with
    (post := {{ (prob (val = k1)) <= #(1 / INR k) * y1 /\ #(1 / INR k) * y1 <= (prob (val = k1)) }}).
  { ptrans; pvalid. split_hyps. lra. }
  apply HAnd.
  - apply HConseqLeft with (pre' := {{ box (#(guard k) /\ #(guard k)) /\ (prob true) <= y1 }}).
    + ptrans; pvalid. split_hyps. split; lra.
    + apply (uniform_k_UB_inter k k1 Hk1).
  - apply HConseqLeft with (pre' := {{ box (#(guard k) /\ #(guard k)) /\ y1 <= (prob true) }}).
    + ptrans; pvalid. split_hyps. split; lra.
    + apply (uniform_k_LB_inter k k1 Hk1).
Qed.

(** Starting at [val = k], [uniform_k k] outputs each [k1 < k] with
    probability [1/k]. *)
Theorem uniform (k k1 : nat) : (k1 < k)%nat ->
  hoare_derivable {{ (prob (val = k)) = 1 /\ (prob (val = k)) = (prob true) }}
    (uniform_k k) {{ #(1 / INR k) = (prob (val = k1)) }}.
Proof.
  intros Hk1.
  apply HConseqLeft with (pre' := {{ (prob (k <= val)) = 1 /\ (prob (k <= val)) = (prob true) }}).
  { ptrans; pvalid. split_hyps.
    pose proof (Pr_mono ps Hps \{ val = k \} \{ k <= val \} ltac:(cdecide)).
    pose proof (Pr_le_true ps Hps \{ k <= val \}).
    pcanon [\{ val = k \}; \{ k <= val \}; \{ true \}]. unfold Pc in *.
    split; lra. }
  assert (Hy : hoare_derivable
                 {{ ((prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true)) /\ y1 = 1 }}
                 (uniform_k k) {{ #(1 / INR k) * y1 = (prob (val = k1)) }}).
  { apply HConseqLeft with (pre' := {{ (prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}).
    - ptrans; pvalid. split_hyps. split; lra.
    - apply (uniform_k_inter k k1 Hk1). }
  eapply HConseq; [|apply (HInstantiate y1 1 _ _ _ Hy)|].
  - ptrans; pvalid. split_hyps. split; [split|]; lra.
  - ptrans; pvalid. lra.
Qed.

End Uniform.
