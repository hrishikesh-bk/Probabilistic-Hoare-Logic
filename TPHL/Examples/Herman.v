(** Herman's self-stabilising protocol, three processes.

    While all three bits agree, every process tosses a fair coin.  The loop
    terminates with probability 1.

    [body1]..[body4] derive the loop body's effect; the two while rules
    ([HWhileUpper], [HWhileLower]) give the upper and lower bounds, combined
    in [Herman_termination_y]; [Herman_termination] instantiates [y] with
    [HInstantiate].  The while rules' precondition is
    [box (guard /\ all_true) /\ Pr(true) <= y] (resp. [>=]).  Their body
    premise is a conjunction [finite_p_and 2 ...] that starts with [p_true];
    that conjunct is derived by [HFree] ([HTrue]). *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms Soundness.AssertionFacts.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module Herman.

Notation a1 := (bool_program_var "a1").
Notation a2 := (bool_program_var "a2").
Notation a3 := (bool_program_var "a3").
Notation y := (prob_logic_var "y").

Notation all_true := (\{ a1 /\ a2 /\ a3 \} : CFormula).
Notation all_false := (\{ ~ a1 /\ ~ a2 /\ ~ a3 \} : CFormula).
Notation guard := (\{ all_true \/ all_false \} : CFormula).
Definition body : Cmd := <{ a1 toss 0.5; a2 toss 0.5; a3 toss 0.5 }>.
Definition Herman : Cmd := CWhile guard body.

(** The two regions of the while rules. *)
Definition regions (i : nat) : CFormula := match i with O => all_true | _ => all_false end.

Ltac herman_auto :=
  unfold regions; pauto [fvar a1; fvar a2; fvar a3].

(** The empty conjunct of [finite_p_and]. *)
Lemma HTrue (pre : PFormula) (c : Cmd) : hoare_derivable pre c p_true.
Proof.
  apply HConseqLeft with (pre' := p_true).
  - intros ps Hps _. apply psatisfies_true.
  - apply HFree. cbn. auto.
Qed.

Lemma half_valid : coin_probability_valid 0.5.
Proof. unfold coin_probability_valid; lra. Qed.

Theorem body1 : hoare_derivable {{ (prob true) = 1 }} body {{ (prob true) = 1 }}.
Proof.
  unfold body.
  apply HSeq with (eta2 := {{ (prob true) = 1 }}).
  - apply HConseqLeft with (pre' := toss_pformula a1 0.5 {{ (prob true) = 1 }}).
    + herman_auto.
    + apply HBoolToss, half_valid.
  - apply HSeq with (eta2 := {{ (prob true) = 1 }}).
    + apply HConseqLeft with (pre' := toss_pformula a2 0.5 {{ (prob true) = 1 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
    + apply HConseqLeft with (pre' := toss_pformula a3 0.5 {{ (prob true) = 1 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
Qed.

Theorem body2 : hoare_derivable {{ (prob true) = 1 }} body {{ (prob (a1 /\ a2 /\ a3)) = 0.125 }}.
Proof.
  unfold body.
  apply HSeq with (eta2 := {{ (prob a1) = 0.5 }}).
  - apply HConseqLeft with (pre' := toss_pformula a1 0.5 {{ (prob a1) = 0.5 }}).
    + herman_auto.
    + apply HBoolToss, half_valid.
  - apply HSeq with (eta2 := {{ (prob (a1 /\ a2)) = 0.25 }}).
    + apply HConseqLeft with (pre' := toss_pformula a2 0.5 {{ (prob (a1 /\ a2)) = 0.25 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
    + apply HConseqLeft
        with (pre' := toss_pformula a3 0.5 {{ (prob (a1 /\ a2 /\ a3)) = 0.125 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
Qed.

Theorem body3 : hoare_derivable {{ (prob true) = 1 }} body
  {{ (prob (~ a1 /\ ~ a2 /\ ~ a3)) = 0.125 }}.
Proof.
  unfold body.
  apply HSeq with (eta2 := {{ (prob (~ a1)) = 0.5 }}).
  - apply HConseqLeft with (pre' := toss_pformula a1 0.5 {{ (prob (~ a1)) = 0.5 }}).
    + herman_auto.
    + apply HBoolToss, half_valid.
  - apply HSeq with (eta2 := {{ (prob (~ a1 /\ ~ a2)) = 0.25 }}).
    + apply HConseqLeft
        with (pre' := toss_pformula a2 0.5 {{ (prob (~ a1 /\ ~ a2)) = 0.25 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
    + apply HConseqLeft
        with (pre' := toss_pformula a3 0.5 {{ (prob (~ a1 /\ ~ a2 /\ ~ a3)) = 0.125 }}).
      * herman_auto.
      * apply HBoolToss, half_valid.
Qed.

Theorem body4 : hoare_derivable {{ (prob true) = 1 }} body {{ (prob (~ guard)) = 0.75 }}.
Proof.
  apply HConseqRight with (post := {{ (prob true) = 1 /\ (prob (a1 /\ a2 /\ a3)) = 0.125 /\
                                      (prob (~ a1 /\ ~ a2 /\ ~ a3)) = 0.125 }}).
  - herman_auto.
  - apply HAnd; [apply body1|]. apply HAnd; [apply body2 | apply body3].
Qed.

(** Body premise of [W^UB]: each region moves to each region with
    probability at most 1/8 and exits with at most 3/4. *)
Lemma body_upper i : (i < 2)%nat ->
  hoare_derivable (p_concentrated_unit (regions i)) body
    (while_body_post_upper 2 regions (fun _ => 1/8) guard c_true 0.75).
Proof.
  intros Hi. unfold while_body_post_upper. cbn [finite_p_and].
  apply HAnd; [apply HAnd; [apply HAnd; [apply HTrue|]|]|].
  - apply HConseq with (eta1 := {{ (prob true) = 1 }})
                       (eta2 := {{ (prob (a1 /\ a2 /\ a3)) = 0.125 }}).
    + herman_auto.
    + apply body2.
    + herman_auto.
  - apply HConseq with (eta1 := {{ (prob true) = 1 }})
                       (eta2 := {{ (prob (~ a1 /\ ~ a2 /\ ~ a3)) = 0.125 }}).
    + herman_auto.
    + apply body3.
    + herman_auto.
  - apply HConseq with (eta1 := {{ (prob true) = 1 }})
                       (eta2 := {{ (prob (~ guard)) = 0.75 }}).
    + herman_auto.
    + apply body4.
    + herman_auto.
Qed.

(** Body premise of [W^LB]: the same bounds from below. *)
Lemma body_lower i : (i < 2)%nat ->
  hoare_derivable (p_concentrated_unit (regions i)) body
    (while_body_post_lower 2 regions (fun _ => 1/8) guard c_true 0.75).
Proof.
  intros Hi. unfold while_body_post_lower. cbn [finite_p_and].
  apply HAnd; [apply HAnd; [apply HAnd; [apply HTrue|]|]|].
  - apply HConseqRight with (post := {{ (prob (a1 /\ a2 /\ a3)) = 0.125 }}).
    + herman_auto.
    + apply HConseqLeft with (pre' := {{ (prob true) = 1 }}).
      * herman_auto.
      * apply body2.
  - apply HConseq with (eta1 := {{ (prob true) = 1 }})
                       (eta2 := {{ (prob (~ a1 /\ ~ a2 /\ ~ a3)) = 0.125 }}).
    + herman_auto.
    + apply body3.
    + herman_auto.
  - apply HConseq with (eta1 := {{ (prob true) = 1 }})
                       (eta2 := {{ (prob (~ guard)) = 0.75 }}).
    + herman_auto.
    + apply body4.
    + herman_auto.
Qed.

Theorem Herman_termination_y_UB :
  hoare_derivable {{ box (guard /\ all_true) /\ (prob true) <= y }} Herman
    {{ (prob true) <= 1 * y }}.
Proof.
  apply (HWhileUpper 2 0 guard c_true body regions (fun _ => 1) (fun _ => 0.75)
           (fun _ _ => 1/8) y).
  - lia.
  - while_side. unfold regions. cdecide.
  - exact body_upper.
  - while_side. below_cases; lra.
Qed.

Theorem Herman_termination_y_LB :
  hoare_derivable {{ box (guard /\ all_true) /\ y <= (prob true) }} Herman
    {{ 1 * y <= (prob true) }}.
Proof.
  apply (HWhileLower 2 0 guard c_true body regions (fun _ => 1) (fun _ => 0.75)
           (fun _ _ => 1/8) y).
  - lia.
  - while_side. below_cases; unfold regions; cdecide.
  - while_side. intros i j Hij1 Hij2. destruct i as [|[|]]; try lia.
    assert (j = 0)%nat by lia; subst. unfold regions. cdecide.
  - while_side. below_cases; left; lra.
  - exact body_lower.
  - while_side. below_cases; lra.
Qed.

Definition pre_y : PFormula :=
  {{ (prob (guard /\ all_true)) = y /\ (prob (guard /\ all_true)) = (prob true) }}.

Theorem Herman_termination_y : hoare_derivable pre_y Herman {{ (prob true) = 1 * y }}.
Proof.
  apply HConseqRight with (post := {{ (prob true) <= 1 * y /\ 1 * y <= (prob true) }}).
  - herman_auto.
  - apply HAnd.
    + apply HConseqLeft with (pre' := {{ box (guard /\ all_true) /\ (prob true) <= y }}).
      * unfold pre_y. herman_auto.
      * apply Herman_termination_y_UB.
    + apply HConseqLeft with (pre' := {{ box (guard /\ all_true) /\ y <= (prob true) }}).
      * unfold pre_y. herman_auto.
      * apply Herman_termination_y_LB.
Qed.

(** Starting with all bits true, Herman's protocol terminates with
    probability 1. *)
Theorem Herman_termination :
  hoare_derivable
    {{ (prob (a1 /\ a2 /\ a3)) = 1 /\ (prob (a1 /\ a2 /\ a3)) = (prob true) }}
    Herman
    {{ (prob true) = 1 }}.
Proof.
  apply HConseq with (eta1 := subst_prob_pformula y (PConst 1) pre_y)
                     (eta2 := subst_prob_pformula y (PConst 1) {{ (prob true) = 1 * y }}).
  - unfold pre_y. herman_auto.
  - apply HInstantiate.
    apply HConseqLeft with (pre' := pre_y).
    + intros ps Hps H. exact H.
    + apply Herman_termination_y.
  - herman_auto.
Qed.

End Herman.
