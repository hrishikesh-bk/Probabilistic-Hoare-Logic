Print Libraries.
From PHL Require Import Maps.
From PHL Require Import PHLTest.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import EqNat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import Lia.
(*From PLF Require Export Imp.*)
(*From PLF Require Export Hoare.*)
From Coq Require Import Reals.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Init.Logic.
From Coq Require Import Lra.
From Coq Require Import String.
(* From Coq Require Import List. *)
Import Vector.VectorNotations.
From Coq Require Import Vector.
Import PHL.



Definition GamblersRuin_Body : Cmd :=
<{
if (x >= 1) 
then (b toss ((2/3)%R);
      (if b then (x := x + 1) else (x := x - 1) end))
else skip
end
}>.

(* Want to prove ->  From x -> 2/3 chance of x-1 and 1/3 chace of x+` *)
Check \{ (x<=1)\}.






(*  Gamblers Ruin Helper theorems     *)

Theorem xlt1_Else: ( forall y1 : string,  hoare_triple ({{((prob  ~(x<=1)) = 1) /\ ((prob  ~(x<=1)) = (prob true)) /\ (y1 = 1) }}) <{skip}> ({{ y1 = (prob ~(x <=1)) }}) ).
Proof.
  - intros. eapply HConseq with (eta1 := ({{((prob  ~(x<=1)) = 1) /\ ((prob  ~(x<=1)) = (prob true)) /\ (y1 = 1) }}) )
                                (eta2 := ({{ y1 = (prob ~(x <=1)) }})) (eta3 := ({{ y1 = (prob ~(x <=1)) }})) (eta4 := ({{ y1 = (prob ~(x <=1)) }})) .
    -- unfold PAImplies. intros. destruct H. destruct H0. rewrite -> H. apply H1.
    -- unfold PAImplies. intros. apply H.
    -- apply HSkip.
Qed.


Theorem xlt1_If: ( forall y2 : string,  hoare_triple ({{((prob true) = 0) /\ (y2 = 0) }}) <{(b toss ((2/3)%R); (if b then (x := x + 1) else (x := x - 1) end))}> 
      ({{ y2 = (prob ~(x <=1)) }}) ).
Proof.
intros. eapply HConseq with (eta1 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta2 := ({{((prob true) = 0) /\ (y2 = 0) }}))
                             (eta3 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta4 :=  ({{ y2 = (prob ~(x <=1)) }})).
 - easy. 
 - unfold PAImplies. intros. destruct H. rewrite -> H0.
  assert (forall st : state, (fun st : state => ~ ((CTermexp_of_Texp (Var x) st) <= (CTermexp_of_nat 1 st))) st ->  ({{true}}) st).
        ---- intros. easy.
        ---- simpl. pose proof (measure_inclusion (fst ps) (fun st : state => ~ ((CTermexp_of_Texp (Var x) st) <= (CTermexp_of_nat 1 st)))
                                                      ({{true}})) as H2. pose proof (H2 H1) as H3. simpl in H.
              assert ((fst ps (fun st : state => ~ (((CTermexp_of_Texp (Var x) st) <= (CTermexp_of_nat 1 st))%nat))) <=
      (PTerm_of_R 0 ps))%R.
          ----- rewrite <- H. apply H3.
          ----- pose proof (positive (fst ps) (fun st : state => ~ ((fst st x) <= (CTermexp_of_nat 1 st)))) as H5. 
              apply Rle_antisym. unfold PTerm_of_R. apply Rge_le in H5. apply H5. apply H4.
 - set (eta := (fun st : Pstate => ((Pteval (Pint {{true}}) st) = (PTerm_of_R 0 st)) /\ ((PTermexp_of_pterm (Pvar y2) st) = (PTerm_of_R 0 st)))). simpl in eta. unfold PTerm_of_R in eta.
   eapply HSeq with (eta1 := eta) (eta2 := eta) (eta3 := eta).
  -- eapply HConseq with (eta1 := eta) (eta3 := eta) (eta4 := eta) (eta2:= (btoss_pt b (2/3)%R eta)).
    2: easy. 2: apply HBToss.
    unfold PAImplies. intros. unfold eta. simpl. unfold btoss_pt. simpl. unfold PTerm_of_R. split.
    --- unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. rewrite <- Rmult_plus_distr_r.
        replace ((2 / 3) + (1 - 2 / 3))%R with 1%R by field. rewrite Rmult_1_l. apply H.
    --- apply H.
 -- eapply HConseq with (eta1:= eta) (eta2:= (psfBpsf eta eta b)) (eta3 := ({{(y2 + y2 = (prob true)) /\ (y2 = 0)}})).
  --- unfold PAImplies. intros. unfold psfBpsf. split. unfold PAcondB. unfold Measure_cond_B. simpl.
      unfold eta. simpl. split. unfold PTerm_of_R. ---- unfold eta in H. destruct H. pose proof empty_measure_inclusion (fst ps).
      unfold assert_of_Prop in H1. pose proof H1 H. specialize (H2 (fun st => True /\ (snd st b))). apply H2. 
---- unfold eta in H. apply H.
---- unfold PAcondB. unfold Measure_cond_B. simpl. unfold eta. simpl. split.
      ----- unfold eta in H. destruct H. pose proof empty_measure_inclusion (fst ps). unfold assert_of_Prop in H1. pose proof H1 H. specialize (H2 (fun st : state => True /\ (~ (snd st b)))). apply H2.
      ----- unfold eta in H. destruct H. apply H0.
--- simpl. unfold eta. unfold PTerm_of_R. unfold PAImplies. intros. split. destruct H. rewrite -> H0 in H. rewrite Rplus_0_l in H. symmetry. apply H. simpl. unfold eta. unfold PTerm_of_R. unfold PAImplies. intros. easy.
--- eapply HAnd. ----- apply HIfThen. 
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x (<{x + 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
                  easy. unfold eta. unfold PAImplies. intros. destruct H. rewrite -> H. assumption. apply HTAsgn.
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x (<{x  - 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
                  easy. unfold eta. unfold PAImplies. intros. destruct H. rewrite -> H. assumption. apply HTAsgn.
      ----- unfold eta. unfold psfBpsf. unfold PAcondB. simpl. unfold Measure_cond_B. simpl. eapply HConseq with (eta2 := (fun ps : Pstate => ((snd ps y2) = (0%R)))) 
(eta1 := (fun ps : Pstate =>
   (((fst ps (fun st : state => True /\ (snd st b))) = (0%R)) /\
    ((snd ps y2) = (0%R))) /\
   (((fst ps (fun st : state => True /\ (~ (snd st b)))) =
     (0%R)) /\ ((snd ps y2) = (0%R))))) (eta3 := (fun st : Pstate => (snd st y2) = (PTerm_of_R 0 st))) (eta4 := (fun st : Pstate => (snd st y2) = (PTerm_of_R 0 st))). 
    ------ unfold PAImplies. intros. simpl. destruct H. destruct H0. apply H1.
    ------ unfold PAImplies. intros. easy.
    ------ unfold PTerm_of_R. apply RigidUnchanged.
Qed.



Theorem GamblersRuin_Body_Stuck: hoare_triple (int_true_eq_one \{ ~(x<=1)\}) GamblersRuin_Body ({{ (prob ~(x <=1)) = 1}}).
Proof.
unfold GamblersRuin_Body. eapply HConseq.

