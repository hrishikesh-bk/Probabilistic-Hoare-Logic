(** Secure multi-party computation of a sum by additive secret sharing.

    Each party [i] splits its input [xi] into shares [ri1], [ri2] (uniform
    dice rolls over {0..p}) and [ri3 := (xi - ri1 - ri2) mod (p+1)]; the
    parties add the shares they receive.  The shares party 1 hands out are
    independent of its input [x1].  The dice roll is the derived command
    [roll] of [KRoll.v], with auxiliary Boolean [rc]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.KRoll.
Require Import Soundness.AssertionFacts.

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

(** The invariant: [x1] is independent of the shares [r11], [r12]. *)
Definition Q (k1 l1 l2 : nat) : PFormula :=
  {{ (prob (x1 = k1 /\ r11 = l1 /\ r12 = l2))
     = (prob (x1 = k1)) * (prob (r11 = l1 /\ r12 = l2)) }}.

Lemma kroll_eq x k p1 p2 :
  kroll_pformula x k (p_eq p1 p2) = p_eq (kroll_pterm x k p1) (kroll_pterm x k p2).
Proof. reflexivity. Qed.

(** [g[x := i]] is [phi /\ i = l]. *)
Ltac point_side :=
  let v := fresh "v" in let i := fresh "i" in
  intros v i; unfold gx; pcompute; vdec; pcompute; cunfold; cdestruct;
  rewrite ?PeanoNat.Nat.eqb_eq, ?PeanoNat.Nat.eqb_neq in *;
  intuition (try congruence; try lia).

Ltac free_side :=
  cbn; repeat split; try discriminate; try exact I.

Theorem MPCMain (k1 l1 l2 p : nat) :
  (p > 0)%nat -> (k1 >= 0)%nat -> (l1 >= 0)%nat -> (l2 >= 0)%nat ->
  (k1 < p)%nat -> (l1 < p)%nat -> (l2 < p)%nat ->
  hoare_derivable {{ (prob true) = 1 }}
    <{ (r11 roll p); ((r12 roll p); (r13 := ((x1 - r11 - r12) mod #((p + 1)%nat)))) }>
    (Q k1 l1 l2).
Proof.
  intros Hp _ _ _ Hk1 Hl1 Hl2.
  apply HSeq with (eta2 := {{ (prob (x1 = k1 /\ r11 = l1))
                              = (prob (x1 = k1)) * (prob (r11 = l1)) }}).
  - eapply HConseqLeft; [|apply HKRoll; free_side].
    intros ps Hps H. rewrite kroll_eq. apply psatisfies_eq in H. apply psatisfies_eq.
    cbn [kroll_pterm pterm_eval] in *.
    rewrite (roll_sum_point r11 p _ \{ x1 = k1 \} l1) by (point_side || lia).
    rewrite (roll_sum_dfree r11 p) by free_side.
    rewrite (roll_sum_point r11 p _ \{ true \} l1) by (point_side || lia).
    rewrite formula_assertion_true in *. unfold pconst in H. cbn in H.
    rewrite <- formula_assertion_true in *. rewrite H. ring.
  - eapply HSeq; [|apply HDomAssign].
    rewrite (subst_dom_pformula_dfree r13 (Q k1 l1 l2)) by free_side.
    eapply HConseqLeft; [|apply HKRoll; free_side].
    intros ps Hps H. unfold Q. rewrite kroll_eq. apply psatisfies_eq in H. apply psatisfies_eq.
    cbn [kroll_pterm pterm_eval] in *.
    rewrite (roll_sum_point r12 p _ \{ x1 = k1 /\ r11 = l1 \} l2) by (point_side || lia).
    rewrite (roll_sum_dfree r12 p) by free_side.
    rewrite (roll_sum_point r12 p _ \{ r11 = l1 \} l2) by (point_side || lia).
    rewrite H. ring.
Qed.

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
Theorem MPCSub (k1 l1 l2 p : nat) (ri1 ri2 ri3 xi : DomProgramVar) :
  (p > 0)%nat -> (k1 < p)%nat -> (l1 < p)%nat -> (l2 < p)%nat ->
  NoDup [ri1; ri2; ri3; xi] -> ~ In ri1 MainVars -> ~ In ri2 MainVars ->
  ~ In ri3 MainVars -> ~ In xi MainVars ->
  hoare_derivable (Q k1 l1 l2)
    <{ (ri1 roll p); ((ri2 roll p); (ri3 := ((xi - ri1 - ri2) mod #((p + 1)%nat)))) }>
    (Q k1 l1 l2).
Proof.
  intros _ _ _ _ _ H1 H2 H3 _.
  apply HSeq with (eta2 := Q k1 l1 l2);
    [|apply HSeq with (eta2 := Q k1 l1 l2)].
  - roll_frame H1.
  - roll_frame H2.
  - assign_frame H3.
Qed.

Theorem MPC2ndLoop (k1 l1 l2 p : nat) (r1i r2i r3i si : DomProgramVar) :
  NoDup [r1i; r2i; r3i; si] -> ~ In si MainVars ->
  hoare_derivable (Q k1 l1 l2) <{ si := ((r1i + r2i + r3i) mod #((p + 1)%nat)) }> (Q k1 l1 l2).
Proof. intros _ H. assign_frame H. Qed.

Theorem MPCFinalAssign (k1 l1 l2 p : nat) (s1 s2 s3 v : DomProgramVar) :
  NoDup [s1; s2; s3; v] -> ~ In v MainVars ->
  hoare_derivable (Q k1 l1 l2) <{ v := ((s1 + s2 + s3) mod #((p + 1)%nat)) }> (Q k1 l1 l2).
Proof. intros _ H. assign_frame H. Qed.

Theorem MPCFull (k1 l1 l2 p : nat) :
  (p > 0)%nat -> (k1 >= 0)%nat -> (l1 >= 0)%nat -> (l2 >= 0)%nat ->
  (k1 < p)%nat -> (l1 < p)%nat -> (l2 < p)%nat ->
  hoare_derivable {{ (prob true) = 1 }}
    <{ ((r11 roll p); ((r12 roll p); (r13 := ((x1 - r11 - r12) mod #((p + 1)%nat)))));
       ((r21 roll p); ((r22 roll p); (r23 := ((x2 - r21 - r22) mod #((p + 1)%nat)))));
       ((r31 roll p); ((r32 roll p); (r33 := ((x3 - r31 - r32) mod #((p + 1)%nat)))));
       ((s1f := ((r11 + r21 + r31) mod #((p + 1)%nat)));
        (s2f := ((r12 + r22 + r32) mod #((p + 1)%nat)));
        (s3f := ((r13 + r23 + r33) mod #((p + 1)%nat))));
       (vf := ((s1f + s2f + s3f) mod #((p + 1)%nat))) }>
    (Q k1 l1 l2).
Proof.
  intros Hp Hk0 Hl10 Hl20 Hk1 Hl1 Hl2.
  eapply HSeq; [apply (MPCMain k1 l1 l2 p); assumption|].
  eapply HSeq; [apply (MPCSub k1 l1 l2 p); try assumption;
                first [repeat constructor; cbn; intuition discriminate | cbn; intuition discriminate]|].
  eapply HSeq; [apply (MPCSub k1 l1 l2 p); try assumption;
                first [repeat constructor; cbn; intuition discriminate | cbn; intuition discriminate]|].
  eapply HSeq.
  - eapply HSeq; [apply (MPC2ndLoop k1 l1 l2 p); first [repeat constructor; cbn; intuition discriminate
                                             | cbn; intuition discriminate]|].
    eapply HSeq; apply (MPC2ndLoop k1 l1 l2 p); first [repeat constructor; cbn; intuition discriminate
                                         | cbn; intuition discriminate].
  - apply (MPCFinalAssign k1 l1 l2 p s1f s2f s3f vf); first [repeat constructor; cbn; intuition discriminate
                                | cbn; intuition discriminate].
Qed.

End MPC.
