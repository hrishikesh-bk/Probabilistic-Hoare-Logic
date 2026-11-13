(** Secure multi-party computation of a sum by additive secret sharing.

    Each party [i] draws two shares [ri1], [ri2] uniformly from {0..p}
    (dice rolls) and sets [ri3 := (xi + 2(p+1) - ri1 - ri2) mod (p+1)], so
    that [ri1 + ri2 + ri3 = xi (mod p+1)]; the term [2(p+1)] keeps the
    truncated subtraction over [nat] non-negative.  Party [i] keeps [ri1] and
    sends [ri2] and [ri3] to the other two parties; party [j] adds the shares
    [r1j + r2j + r3j] it holds, and the three partial sums are added.

    [MPCFull]: the two shares party 1 sends out, [r12] and [r13], are jointly
    independent of its input [x1].  The dice roll is the derived command
    [roll] of [KRoll.v], with auxiliary Boolean [rc]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
Require Import PHL Examples.Lib Examples.KRoll.
Require Import Soundness.StateFacts Soundness.AssertionFacts.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module MPC.

Notation rc := (bool_program_var "roll_c").
Notation x1 := (dom_program_var "x1").
Notation x2 := (dom_program_var "x2").
Notation x3 := (dom_program_var "x3").
Notation r11 := (dom_program_var "r11").
Notation r12 := (dom_program_var "r12").
Notation r13 := (dom_program_var "r13").
Notation r21 := (dom_program_var "r21").
Notation r22 := (dom_program_var "r22").
Notation r23 := (dom_program_var "r23").
Notation r31 := (dom_program_var "r31").
Notation r32 := (dom_program_var "r32").
Notation r33 := (dom_program_var "r33").
Notation s1f := (dom_program_var "s1").
Notation s2f := (dom_program_var "s2").
Notation s3f := (dom_program_var "s3").
Notation vf := (dom_program_var "v").

(** [x roll k]: draw [x] uniformly from {0, ..., k} (see [KRoll.v]). *)
Notation "x 'roll' k" := (roll rc x k)
  (in custom tcom at level 0, x constr at level 0, k constr at level 0) : tphl_scope.

(** [2(p+1)], added before subtracting the two random shares. *)
Definition shift (p : nat) : nat := (2 * (p + 1))%nat.

(** The invariant: [x1] is independent of the shares [r12], [r13]. *)
Definition Q (k1 l2 l3 : nat) : PFormula :=
  {{ (prob (x1 = k1 /\ r12 = l2 /\ r13 = l3))
     = (prob (x1 = k1)) * (prob (r12 = l2 /\ r13 = l3)) }}.

(** * Arithmetic of the third share *)

(** For fixed [x], [l2] and [l3], exactly one [i <= p] makes the third share
    equal to [l3]. *)
Lemma share_eq (x i l2 l3 p : nat) : (i <= p)%nat -> (l2 <= p)%nat -> (l3 <= p)%nat ->
  (((x + shift p - i - l2) mod (p + 1) = l3)%nat <->
   (i = (x + shift p - l2 - l3) mod (p + 1))%nat).
Proof.
  unfold shift. intros Hi Hl2 Hl3.
  assert (Hab : (x + 2 * (p + 1) - i - l2 + i = x + 2 * (p + 1) - l2 - l3 + l3)%nat) by lia.
  split; intros H.
  - pose proof (Nat.div_mod_eq (x + 2 * (p + 1) - i - l2) (p + 1)) as Ha.
    rewrite H in Ha.
    set (q := ((x + 2 * (p + 1) - i - l2) / (p + 1))%nat) in *.
    apply (Nat.mod_unique _ _ q); [lia|].
    set (t := ((p + 1) * q)%nat) in *. lia.
  - pose proof (Nat.div_mod_eq (x + 2 * (p + 1) - l2 - l3) (p + 1)) as Hb.
    rewrite <- H in Hb.
    set (q := ((x + 2 * (p + 1) - l2 - l3) / (p + 1))%nat) in *.
    symmetry. apply (Nat.mod_unique _ _ q); [lia|].
    set (t := ((p + 1) * q)%nat) in *. lia.
Qed.

(** * Sums over a dice roll *)

(** [roll_sum_point] when [g[x := i]] is [phi /\ i = l] only for [i <= k]
    (the values the roll can take). *)
Lemma roll_sum_point_le (x : DomProgramVar) k g phi l ps :
  (forall v i, (i <= k)%nat -> (satisfies v (gx x g i) <-> satisfies v phi /\ i = l)) ->
  (l <= k)%nat ->
  pterm_eval (roll_sum x k g (S k) O) ps = / INR (S k) * Pr[ps] phi.
Proof.
  intros Hg Hl. rewrite roll_sum_eval.
  erewrite sumn_ext.
  2:{ intros i Hi. cbn [Nat.add].
      replace (Pr[ps] (gx x g i)) with (if Nat.eqb i l then Pr[ps] phi else 0).
      - reflexivity.
      - destruct (Nat.eqb i l) eqn:E.
        + apply Nat.eqb_eq in E; subst. apply Pr_ext; intro v.
          rewrite (Hg v l ltac:(lia)); tauto.
        + apply Nat.eqb_neq in E. rewrite <- (Pr_false ps).
          apply Pr_ext; intro v; rewrite (Hg v i ltac:(lia)); cbn; tauto. }
  rewrite <- sumn_scale. rewrite sumn_indicator by lia. reflexivity.
Qed.

Fixpoint big_or (m : nat) (F : nat -> CFormula) : CFormula :=
  match m with
  | O => FFalse
  | S m' => c_or (F O) (big_or m' (fun i => F (S i)))
  end.

Lemma satisfies_big_or m F v :
  satisfies v (big_or m F) <-> exists i, (i < m)%nat /\ satisfies v (F i).
Proof.
  revert F; induction m as [|m IH]; intros F; cbn [big_or].
  - cbn. split; [tauto|]. intros [i [Hi _]]. lia.
  - rewrite satisfies_or, IH. split.
    + intros [H|[i [Hi H]]]; [exists O | exists (S i)]; split; auto; lia.
    + intros [[|i] [Hi H]]; [left; exact H | right; exists i; split; auto; lia].
Qed.

Lemma Pr_sumn_disjoint ps m F : pstate_admissible ps ->
  (forall v i j, (i < m)%nat -> (j < m)%nat -> satisfies v (F i) -> satisfies v (F j) -> i = j) ->
  sumn (fun i => Pr[ps] (F i)) m = Pr[ps] (big_or m F).
Proof.
  intros Hps. revert F; induction m as [|m IH]; intros F Hu; cbn [sumn big_or].
  - rewrite Pr_false. reflexivity.
  - rewrite (Pr_disjoint ps Hps).
    + rewrite (IH (fun i => F (S i))); [reflexivity|].
      intros v i j Hi Hj H1 H2. assert (S i = S j) by (apply (Hu v); auto; lia). lia.
    + intros v [H0 Hr]. apply satisfies_big_or in Hr as [i [Hi Hs]].
      assert (O = S i) by (apply (Hu v); auto; lia). lia.
Qed.

(** If every valuation satisfies [g[x := i]] for exactly one [i <= k],
    rolling [x] keeps [1/(k+1)] of the total mass. *)
Lemma roll_sum_partition (x : DomProgramVar) k g ps : pstate_admissible ps ->
  (forall v i j, (i <= k)%nat -> (j <= k)%nat ->
     satisfies v (gx x g i) -> satisfies v (gx x g j) -> i = j) ->
  (forall v, exists i, (i <= k)%nat /\ satisfies v (gx x g i)) ->
  pterm_eval (roll_sum x k g (S k) O) ps = / INR (S k) * Pr[ps] c_true.
Proof.
  intros Hps Hu He. rewrite roll_sum_eval, <- sumn_scale. f_equal.
  change (sumn (fun i => Pr[ps] (gx x g i)) (S k) = Pr[ps] c_true).
  rewrite (Pr_sumn_disjoint ps (S k) (fun i => gx x g i) Hps)
    by (intros v i j Hi Hj; apply Hu; lia).
  apply Pr_ext. intros v. rewrite satisfies_big_or. split; intros _.
  - apply satisfies_true.
  - destruct (He v) as [i [Hi H]]. exists i. split; [lia|exact H].
Qed.

(** * Party 1 *)

Lemma kroll_eq x k p1 p2 :
  kroll_pformula x k (p_eq p1 p2) = p_eq (kroll_pterm x k p1) (kroll_pterm x k p2).
Proof. reflexivity. Qed.

Ltac free_side :=
  cbn; repeat split; try discriminate; try exact I.

(** Side conditions of [roll_sum_point]/[roll_sum_point_le]: open the
    substituted formula into arithmetic over the valuation. *)
Ltac open_side :=
  unfold gx; pcompute; vdec; pcompute; cunfold; rewrite ?Nat.eqb_eq.

(** The share of party 1 after rolling [r12 = l2], as a formula over [r11]. *)
Definition E (p l2 l3 : nat) : CFormula :=
  \{ (x1 + #(shift p) - r11 - l2) mod #((p + 1)%nat) = l3 \}.

Theorem MPCMain (k1 l2 l3 p : nat) :
  (p > 0)%nat -> (l2 <= p)%nat -> (l3 <= p)%nat ->
  hoare_derivable {{ (prob true) = 1 }}
    <{ (r11 roll p);
       ((r12 roll p); (r13 := ((x1 + #(shift p) - r11 - r12) mod #((p + 1)%nat)))) }>
    (Q k1 l2 l3).
Proof.
  intros Hp Hl2 Hl3.
  apply HSeq with (eta2 := p_eq (PProb (c_and \{ x1 = k1 \} (E p l2 l3)))
                               (PMul (PProb \{ x1 = k1 \}) (PProb (E p l2 l3)))).
  - eapply HConseqLeft; [|apply HKRoll; free_side].
    intros ps Hps H. rewrite kroll_eq. apply psatisfies_eq in H. apply psatisfies_eq.
    cbn [kroll_pterm pterm_eval] in *.
    rewrite (roll_sum_point_le r11 p _ \{ x1 = k1 \} ((k1 + shift p - l2 - l3) mod (p + 1))).
    2:{ intros v i Hi. unfold E. open_side.
        set (X := dom_program_values v x1).
        destruct (Nat.eq_dec X k1) as [->|Hne].
        - rewrite (share_eq k1 i l2 l3 p Hi Hl2 Hl3). tauto.
        - tauto. }
    2:{ pose proof (Nat.mod_upper_bound (k1 + shift p - l2 - l3) (p + 1) ltac:(lia)). lia. }
    rewrite (roll_sum_dfree r11 p) by free_side.
    rewrite (roll_sum_partition r11 p (E p l2 l3) ps Hps).
    3:{ intros v. exists ((dom_program_values v x1 + shift p - l2 - l3) mod (p + 1))%nat.
        pose proof (Nat.mod_upper_bound (dom_program_values v x1 + shift p - l2 - l3) (p + 1)
                      ltac:(lia)).
        split; [lia|]. unfold E. open_side.
        apply share_eq; [lia | exact Hl2 | exact Hl3 | reflexivity]. }
    2:{ intros v i j Hi Hj Hsi Hsj. unfold E in *. revert Hsi Hsj. open_side.
        rewrite (share_eq _ i l2 l3 p Hi Hl2 Hl3), (share_eq _ j l2 l3 p Hj Hl2 Hl3).
        intros -> ->. reflexivity. }
    rewrite formula_assertion_true in *. unfold pconst in H. cbn in H.
    rewrite <- formula_assertion_true in *. rewrite H. ring.
  - apply HSeq with
      (eta2 := {{ (prob (x1 = k1 /\ r12 = l2 /\
                         (x1 + #(shift p) - r11 - r12) mod #((p + 1)%nat) = l3))
                  = (prob (x1 = k1)) *
                    (prob (r12 = l2 /\ (x1 + #(shift p) - r11 - r12) mod #((p + 1)%nat) = l3)) }}).
    + eapply HConseqLeft; [|apply HKRoll; free_side].
      intros ps Hps H. rewrite kroll_eq. apply psatisfies_eq in H. apply psatisfies_eq.
      cbn [kroll_pterm pterm_eval] in *.
      rewrite (roll_sum_point r12 p _ (c_and \{ x1 = k1 \} (E p l2 l3)) l2).
      2:{ intros v i. unfold E. open_side.
          destruct (Nat.eq_dec i l2) as [->|Hne]; tauto. }
      2:{ exact Hl2. }
      rewrite (roll_sum_dfree r12 p) by free_side.
      rewrite (roll_sum_point r12 p _ (E p l2 l3) l2).
      2:{ intros v i. unfold E. open_side.
          destruct (Nat.eq_dec i l2) as [->|Hne]; tauto. }
      2:{ exact Hl2. }
      rewrite H. ring.
    + eapply HConseqLeft; [|apply HDomAssign].
      intros ps _ H. exact H.
Qed.

(** * The other parties *)

Definition MainVars := [r11; r12; r13; x1].

Ltac frame_side H :=
  cbn; repeat split; intros Heq; apply H; subst; cbn; tauto.

(** [HConseqLeft] + [HKRoll] for a roll of a variable [Q] does not mention. *)
Ltac roll_frame H :=
  eapply HConseqLeft; [|apply HKRoll; free_side];
  intros ps _ Hq; apply kroll_pformula_dfree; [frame_side H | exact Hq].

(** [HConseqLeft] + [HDomAssign] for an assignment to a variable [Q] does
    not mention. *)
Ltac assign_frame H :=
  eapply HConseqLeft; [|apply HDomAssign];
  intros ps _ Hq; rewrite subst_dom_pformula_dfree by frame_side H; exact Hq.

(** The other parties' share generation does not touch party 1's variables. *)
Theorem MPCSub (k1 l2 l3 p : nat) (ri1 ri2 ri3 xi : DomProgramVar) :
  NoDup [ri1; ri2; ri3; xi] -> ~ In ri1 MainVars -> ~ In ri2 MainVars ->
  ~ In ri3 MainVars -> ~ In xi MainVars ->
  hoare_derivable (Q k1 l2 l3)
    <{ (ri1 roll p);
       ((ri2 roll p); (ri3 := ((xi + #(shift p) - ri1 - ri2) mod #((p + 1)%nat)))) }>
    (Q k1 l2 l3).
Proof.
  intros _ H1 H2 H3 _.
  apply HSeq with (eta2 := Q k1 l2 l3);
    [|apply HSeq with (eta2 := Q k1 l2 l3)].
  - roll_frame H1.
  - roll_frame H2.
  - assign_frame H3.
Qed.

Theorem MPC2ndLoop (k1 l2 l3 p : nat) (r1i r2i r3i si : DomProgramVar) :
  NoDup [r1i; r2i; r3i; si] -> ~ In si MainVars ->
  hoare_derivable (Q k1 l2 l3) <{ si := ((r1i + r2i + r3i) mod #((p + 1)%nat)) }> (Q k1 l2 l3).
Proof. intros _ H. assign_frame H. Qed.

Theorem MPCFinalAssign (k1 l2 l3 p : nat) (s1 s2 s3 v : DomProgramVar) :
  NoDup [s1; s2; s3; v] -> ~ In v MainVars ->
  hoare_derivable (Q k1 l2 l3) <{ v := ((s1 + s2 + s3) mod #((p + 1)%nat)) }> (Q k1 l2 l3).
Proof. intros _ H. assign_frame H. Qed.

(** The whole protocol: for every input value [k1] of party 1 and all share
    values [l2, l3 <= p], the shares [r12], [r13] that party 1 sends out are
    jointly independent of [x1]. *)
Theorem MPCFull (k1 l2 l3 p : nat) :
  (p > 0)%nat -> (l2 <= p)%nat -> (l3 <= p)%nat ->
  hoare_derivable {{ (prob true) = 1 }}
    <{ ((r11 roll p); ((r12 roll p);
         (r13 := ((x1 + #(shift p) - r11 - r12) mod #((p + 1)%nat)))));
       ((r21 roll p); ((r22 roll p);
         (r23 := ((x2 + #(shift p) - r21 - r22) mod #((p + 1)%nat)))));
       ((r31 roll p); ((r32 roll p);
         (r33 := ((x3 + #(shift p) - r31 - r32) mod #((p + 1)%nat)))));
       ((s1f := ((r11 + r21 + r31) mod #((p + 1)%nat)));
        (s2f := ((r12 + r22 + r32) mod #((p + 1)%nat)));
        (s3f := ((r13 + r23 + r33) mod #((p + 1)%nat))));
       (vf := ((s1f + s2f + s3f) mod #((p + 1)%nat))) }>
    (Q k1 l2 l3).
Proof.
  intros Hp Hl2 Hl3.
  eapply HSeq; [apply (MPCMain k1 l2 l3 p); assumption|].
  eapply HSeq; [apply (MPCSub k1 l2 l3 p);
                first [repeat constructor; cbn; intuition discriminate | cbn; intuition discriminate]|].
  eapply HSeq; [apply (MPCSub k1 l2 l3 p);
                first [repeat constructor; cbn; intuition discriminate | cbn; intuition discriminate]|].
  eapply HSeq.
  - eapply HSeq; [apply (MPC2ndLoop k1 l2 l3 p); first [repeat constructor; cbn; intuition discriminate
                                             | cbn; intuition discriminate]|].
    eapply HSeq; apply (MPC2ndLoop k1 l2 l3 p); first [repeat constructor; cbn; intuition discriminate
                                         | cbn; intuition discriminate].
  - apply (MPCFinalAssign k1 l2 l3 p s1f s2f s3f vf); first [repeat constructor; cbn; intuition discriminate
                                | cbn; intuition discriminate].
Qed.

End MPC.
