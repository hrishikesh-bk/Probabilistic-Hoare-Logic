(** Rejection sampling (ported from the old [RejectionSampling.v]).

    [b0 := tt; b1 := tt; while (b0 /\ b1) do toss(b0, 1/2); toss(b1, 1/2)]
    ends with [b0 /\ ~b1] with probability exactly 1/3.

    The proofs follow the old file rule by rule; only the side conditions are
    proved differently.  Differences forced by TPHL:
    - [HWhileUB]/[HWhileLB] become [HWhileUpper]/[HWhileLower], whose
      precondition is [box (guard /\ (b0 /\ b1)) /\ Pr(true) <= y] (resp.
      [>=]); the old auxiliary arguments [beta], [tempA] (which only matched
      the old rule's syntax) are dropped.
    - The rules' body premise starts from [p_concentrated_unit guard]; one
      [HConseqLeft] turns it into the precondition of [Rsampling_body]
      (the old [int_true_eq_one] premise was that precondition already).
    - [eliminate_y] is [HInstantiate].
    - [Rejection_sampling_correct] (the two assignments before the loop) is
      new. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module RejectionSampling.

Notation b0 := (bool_program_var "b0").
Notation b1 := (bool_program_var "b1").
Notation y := (prob_logic_var "y").

Notation half := (0.5 : R).

Definition body : Cmd := <{ b0 toss half; b1 toss half }>.

Definition Rejection_sampling : Cmd :=
  <{ b0 b= true; b1 b= true; while (b0 /\ b1) do body end }>.

Definition one_third : R := 1/3.

Theorem Rsampling_body :
  hoare_derivable
    {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}
    body
    {{ (prob (b0 /\ b1)) = 0.25 /\ (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }}.
Proof.
  apply HSeq with (eta2 := {{ (prob b0) = 0.5 }}).
  - apply HConseqLeft with (pre' := toss_pformula b0 half {{ (prob b0) = 0.5 }}).
    + pauto [fvar b0; fvar b1].
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HAnd.
    + apply HConseqLeft with (pre' := toss_pformula b1 half {{ (prob (b0 /\ b1)) = 0.25 }}).
      * pauto [fvar b0; fvar b1].
      * apply HBoolToss. unfold coin_probability_valid; lra.
    + apply HConseqRight with (post := {{ (prob (b0 /\ ~ b1)) = 0.25 }}).
      * pauto [fvar b0; fvar b1].
      * apply HConseqLeft
          with (pre' := toss_pformula b1 half {{ (prob (b0 /\ ~ b1)) = 0.25 }}).
        -- pauto [fvar b0; fvar b1].
        -- apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Definition guard : CFormula := \{ b0 /\ b1 \}.
Definition loop : Cmd := CWhile guard body.

(** [W^UB] with one region [b0 /\ b1]: [Pr(b0 /\ ~b1) <= 1/3 * y]. *)
Theorem Rsampling_loop_y :
  hoare_derivable
    {{ box (guard /\ (b0 /\ b1)) /\ (prob true) <= y }}
    loop
    {{ (prob (b0 /\ ~ b1)) <= one_third * y }}.
Proof.
  apply (HWhileUpper 1 0 guard \{ b0 /\ ~ b1 \} body (fun _ => \{ b0 /\ b1 \})
           (fun _ => one_third) (fun _ => 0.25) (fun _ _ => 0.25) y).
  - lia.
  - while_side. unfold guard. cdecide.
  - below_cases.
    apply HConseqLeft
      with (pre' := {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}).
    + pauto [fvar b0; fvar b1].
    + apply HConseqRight with (post := {{ (prob (b0 /\ b1)) = 0.25 /\
                                          (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }}).
      * unfold guard. pauto [fvar b0; fvar b1].
      * apply Rsampling_body.
  - while_side. below_cases. unfold one_third. lra.
Qed.

Theorem Rsampling_loop :
  hoare_derivable
    {{ (prob (b0 /\ b1)) <= y /\ (prob (b0 /\ b1)) = (prob true) }}
    loop
    {{ (prob (b0 /\ ~ b1)) <= one_third * y }}.
Proof.
  apply HConseqLeft with (pre' := {{ box (guard /\ (b0 /\ b1)) /\ (prob true) <= y }}).
  - unfold guard. pauto [fvar b0; fvar b1].
  - apply Rsampling_loop_y.
Qed.

Theorem RsamplingUB :
  hoare_derivable
    {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}
    loop
    {{ (prob (b0 /\ ~ b1)) <= one_third }}.
Proof.
  apply HConseqLeft with (pre' := {{ (prob (b0 /\ b1)) <= 1 /\ (prob (b0 /\ b1)) = (prob true) }}).
  - pauto [fvar b0; fvar b1].
  - apply HConseq
      with (eta1 := subst_prob_pformula y (PConst 1)
                      {{ (prob (b0 /\ b1)) <= y /\ (prob (b0 /\ b1)) = (prob true) }})
           (eta2 := subst_prob_pformula y (PConst 1)
                      {{ (prob (b0 /\ ~ b1)) <= one_third * y }}).
    + pauto [fvar b0; fvar b1].
    + apply HInstantiate.
      apply HConseqLeft
        with (pre' := {{ (prob (b0 /\ b1)) <= y /\ (prob (b0 /\ b1)) = (prob true) }}).
      * intros ps Hps H. exact H.
      * apply Rsampling_loop.
    + unfold one_third. pauto [fvar b0; fvar b1].
Qed.

(** [W^LB] with the same region: [Pr(b0 /\ ~b1) >= 1/3 * y]. *)
Theorem Rsampling_loop_LB_y :
  hoare_derivable
    {{ box (guard /\ (b0 /\ b1)) /\ y <= (prob true) }}
    loop
    {{ one_third * y <= (prob (b0 /\ ~ b1)) }}.
Proof.
  apply (HWhileLower 1 0 guard \{ b0 /\ ~ b1 \} body (fun _ => \{ b0 /\ b1 \})
           (fun _ => one_third) (fun _ => 0.25) (fun _ _ => 0.25) y).
  - lia.
  - while_side. below_cases. unfold guard. cdecide.
  - while_side. intros i j Hi Hj. lia.
  - while_side. below_cases. left. lra.
  - below_cases.
    apply HConseqLeft
      with (pre' := {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}).
    + pauto [fvar b0; fvar b1].
    + apply HConseqRight with (post := {{ (prob (b0 /\ b1)) = 0.25 /\
                                          (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }}).
      * unfold guard. pauto [fvar b0; fvar b1].
      * apply Rsampling_body.
  - while_side. below_cases. unfold one_third. lra.
Qed.

Theorem Rsampling_loop_LB :
  hoare_derivable
    {{ y <= (prob (b0 /\ b1)) /\ (prob (b0 /\ b1)) = (prob true) }}
    loop
    {{ one_third * y <= (prob (b0 /\ ~ b1)) }}.
Proof.
  apply HConseqLeft with (pre' := {{ box (guard /\ (b0 /\ b1)) /\ y <= (prob true) }}).
  - unfold guard. pauto [fvar b0; fvar b1].
  - apply Rsampling_loop_LB_y.
Qed.

Theorem RsamplingLB :
  hoare_derivable
    {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}
    loop
    {{ one_third <= (prob (b0 /\ ~ b1)) }}.
Proof.
  apply HConseqLeft with (pre' := {{ 1 <= (prob (b0 /\ b1)) /\ (prob (b0 /\ b1)) = (prob true) }}).
  - pauto [fvar b0; fvar b1].
  - apply HConseq
      with (eta1 := subst_prob_pformula y (PConst 1)
                      {{ y <= (prob (b0 /\ b1)) /\ (prob (b0 /\ b1)) = (prob true) }})
           (eta2 := subst_prob_pformula y (PConst 1)
                      {{ one_third * y <= (prob (b0 /\ ~ b1)) }}).
    + pauto [fvar b0; fvar b1].
    + apply HInstantiate.
      apply HConseqLeft
        with (pre' := {{ y <= (prob (b0 /\ b1)) /\ (prob (b0 /\ b1)) = (prob true) }}).
      * intros ps Hps H. exact H.
      * apply Rsampling_loop_LB.
    + unfold one_third. pauto [fvar b0; fvar b1].
Qed.

(** Rejection sampling outputs [b0 /\ ~b1] with probability exactly 1/3. *)
Theorem Rsampling :
  hoare_derivable
    {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}
    loop
    {{ (prob (b0 /\ ~ b1)) = one_third }}.
Proof.
  apply HConseqRight with (post := {{ one_third <= (prob (b0 /\ ~ b1)) /\
                                      (prob (b0 /\ ~ b1)) <= one_third }}).
  - pauto [fvar b0; fvar b1].
  - apply HAnd; [apply RsamplingLB | apply RsamplingUB].
Qed.

(** The whole program: the two assignments establish the loop's precondition. *)
Theorem Rejection_sampling_correct :
  hoare_derivable {{ (prob true) = 1 }} Rejection_sampling {{ (prob (b0 /\ ~ b1)) = one_third }}.
Proof.
  unfold Rejection_sampling.
  apply HSeq with (eta2 := {{ (prob b0) = 1 /\ (prob b0) = (prob true) }}).
  - apply HConseqLeft
      with (pre' := subst_bool_pformula b0 \{ true \} {{ (prob b0) = 1 /\ (prob b0) = (prob true) }}).
    + pauto [fvar b0; fvar b1].
    + apply HBoolAssign.
  - apply HSeq with (eta2 := {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}).
    + apply HConseqLeft
        with (pre' := subst_bool_pformula b1 \{ true \}
                        {{ (prob (b0 /\ b1)) = 1 /\ (prob (b0 /\ b1)) = (prob true) }}).
      * pauto [fvar b0; fvar b1].
      * apply HBoolAssign.
    + exact Rsampling.
Qed.

End RejectionSampling.
