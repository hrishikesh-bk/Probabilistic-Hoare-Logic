From PHL Require Import Maps.
From PHL Require Import PHLTest.
From PHL Require Import Uniform.
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
From Coq Require Import Notations.
From Coq Require Import List.
Import List.ListNotations.
Import PHL.

Definition x : string := "x".
Definition b : string := "b".
Definition y1 : string := "y1".
Definition y2 : string := "y2".

Definition RandomWalk : Cmd :=
<{
  while (1 <= x) do 
    b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
end
}>.

Theorem ifthen_01 : forall (k : nat), hoare_triple ({{((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true) ) /\ y1 = 0.25}}) (<{ x := x+1 }>) 
                                                    ({{(prob (x = (k + 1))) = y1}}).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x <{x+1}> ({{(prob (x = (k + 1))) = y1}})).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps
    (fun st : state =>
     (((CTermexp_of_nat k (x !-> (fst st x) + 1; (fst st), snd st)) +
       (CTermexp_of_nat 1 (x !-> (fst st x) + 1; (fst st), snd st)))%nat) =
     ((x !-> ((fst st x) + 1)%nat; (fst st)) x))) with (fst ps (fun st : state => (CTermexp_of_nat k st) = (fst st x))).
          transitivity (0.25%R). easy. easy. apply equivalence. intro. rewrite t_update_eq. uncoerce_basic. lia. 
        + apply HTAsgn.
Qed.

Theorem ifthen_02 : forall (k : nat), hoare_triple ({{((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true) ) /\ y2 = 0}}) (<{ x := x-1 }>) 
                                                    ({{(prob (x = (k + 1))) = y2}}).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x <{ x - 1 }> ({{(prob (x = (k + 1))) = y2}})).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. uncoerce_basic. replace (fst ps (fun st : state => ((k + 1)%nat) = ((x !-> (fst st x) - 1; (fst st)) x))) with (fst ps (fun st : state => ((k + 1)%nat) = ((fst st x) - 1))).
          rewrite measure_true_dest with (Q := (fun st : state => k = (fst st x))). intro. destruct H. destruct H. symmetry in H1.
          apply Rplus_0_r_uniq in H1. transitivity 0%R. apply measure_inclusion_0 with (Q:= (fun st : state => k <> (fst st x))). intro. lia. easy. easy.
          apply equivalence. intro. rewrite t_update_eq. lia.
        + apply HTAsgn.
Qed.

Theorem ifthen_0_int : forall (k : nat), hoare_triple ({{((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) ))/\ y1 = 0.25) /\ y2 = 0}})
              (<{if b then x := x + 1 else x := x - 1 end}>)
              {{ y1 + y2 = (prob (x = (k + 1))) }}.
Proof. intro. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true) ) /\ y1 = 0.25}}) ({{((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true) ) /\ y2 = 0}}) (b) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. replace (fst ps (fun st : state => True /\ (snd st b))) with (fst ps (fun st : state => snd st b)).
        replace (fst ps (fun st : state => True /\ (~ (snd st b)))) with (fst ps (fun st : state => ~ (snd st b))).  easy.
        apply equivalence. easy. apply equivalence. easy.
      * apply HIfThen. 
        + uncoerce_basic. pose ifthen_01 as H. uncoerce_basic_H H. apply HConseqRight with (eta2 := (fun st : Pstate => (fst st (fun st0 : state => ((k + 1)%nat) = (fst st0 x))) = (snd st y1))).
          intro. easy.  easy.
        + uncoerce_basic. pose ifthen_02 as H. uncoerce_basic_H H. apply HConseqRight with (eta2 := (fun st : Pstate => (fst st (fun st0 : state => ((k + 1)%nat) = (fst st0 x))) = (snd st y2))).
          intro. easy. easy. 
Qed.


Theorem ifthen_0 : forall (k : nat), hoare_triple ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})
              (<{if b then x := x + 1 else x := x - 1 end}>)
          {{ 0.25 = (prob (x = (k + 1))) }}.
Proof. intro. apply HConseq with (eta2 := eta_update_y_p ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }}) y1 0.25%R)
                          (eta3 := eta_update_y_p ({{ y1 + 0 = (prob (x = (k + 1))) }}) y1 0.25%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. unfold PTerm_of_R. rewrite Rplus_0_r. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) ))/\ y1 = 0.25)}}) y2 0%R)
                                                            (eta3 := eta_update_y_p ({{ y1 + y2 = (prob (x = (k + 1))) }}) y2 0%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. easy. 
            easy.
          * apply eliminate_y. easy. easy. apply ifthen_0_int.
Qed.

Theorem ifthen_11 : forall (k : nat), hoare_triple ({{((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true) ) /\ y1 = 0}}) (<{ x := x+1 }>) 
                                                    (fun ps :Pstate => (fst ps (fun st : state => ((k - 1) = fst st x)%nat) = snd ps y1)).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x <{x+1}> (fun ps :Pstate => (fst ps (fun st : state => ((k - 1) = fst st x)%nat) = snd ps y1))).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. uncoerce_basic.
          intro. replace (fst ps (fun st : state => ((k - 1)%nat) = ((x !-> ((fst st x) + 1)%nat; (fst st)) x))) with
                        (fst ps (fun st : state => (k - 1)%nat = ((fst st x) + 1)%nat)). destruct H. destruct H. rewrite H0.
                        apply measure_P_eq_true in H1.  apply measure_inclusion_0 with (Q := (fun st : state => k <> (fst st x))).
                        intro. lia. easy.  apply equivalence. intro. rewrite t_update_eq. uncoerce_basic. lia. 
        + apply HTAsgn.
Qed.

Theorem ifthen_12 : forall (k : nat), (k > 0) -> hoare_triple ({{((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true) ) /\ y2 = 0.75}}) (<{ x := x-1 }>) 
                                                    (fun ps :Pstate => (fst ps (fun st : state => ((k - 1) = fst st x)%nat) = snd ps y2)).
Proof. intros. apply HConseqLeft with (eta2 := tasgn_pt x <{ x - 1 }> (fun ps :Pstate => (fst ps (fun st : state => ((k - 1) = fst st x)%nat) = snd ps y2))).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. uncoerce_basic. replace (fst ps (fun st : state => ((k - 1)%nat) = ((x !-> (fst st x) - 1; (fst st)) x))) with (fst ps (fun st : state => ((k)%nat) = ((fst st x)))).
          intro. transitivity (0.75%R). easy. easy. apply equivalence. intro. rewrite t_update_eq. split. lia. admit.
        + apply HTAsgn. 
Admitted.

Theorem ifthen_1_int : forall (k : nat), (k > 0) -> hoare_triple ({{((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) ))/\ y1 = 0) /\ y2 = 0.75}})
              (<{if b then x := x + 1 else x := x - 1 end}>)
              (fun ps :Pstate => (snd ps y1 + snd ps y2)%R = (fst ps (fun st : state => ((k - 1) = fst st x)%nat) )).
Proof. intros. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true) ) /\ y1 = 0}}) ({{((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true) ) /\ y2 = 0.75}}) (b) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. replace (fst ps (fun st : state => True /\ (snd st b))) with (fst ps (fun st : state => snd st b)).
        replace (fst ps (fun st : state => True /\ (~ (snd st b)))) with (fst ps (fun st : state => ~ (snd st b))).  easy.
        apply equivalence. easy. apply equivalence. easy.
      * apply HIfThen. 
        + uncoerce_basic. pose ifthen_11 as H1. uncoerce_basic_H H1. apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => ((k - 1)%nat) = (fst st x))) = (snd ps y1))).
          intro. easy.  easy.
        + uncoerce_basic. pose ifthen_12 as H1. uncoerce_basic_H H1. apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => ((k - 1)%nat) = (fst st x))) = (snd ps y2))).
          intro. easy. apply H1. easy. 
Qed.


Theorem ifthen_1 : forall (k : nat), (k > 0) -> hoare_triple ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})
              (<{if b then x := x + 1 else x := x - 1 end}>)
          (fun ps :Pstate => (0.75)%R = (fst ps (fun st : state => ((k - 1) = fst st x)%nat) )).
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }}) y1 0%R)
                          (eta3 := eta_update_y_p (fun ps :Pstate => (snd ps y1 + 0.75)%R = (fst ps (fun st : state => ((k - 1) = fst st x)%nat) )) y1 0%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. unfold PTerm_of_R. rewrite Rplus_0_l. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) ))/\ y1 = 0)}}) y2 0.75%R)
                                                            (eta3 := eta_update_y_p (fun ps :Pstate => (snd ps y1 + snd ps y2)%R = (fst ps (fun st : state => ((k - 1) = fst st x)%nat) )) y2 0.75%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. easy. 
            easy.
          * apply eliminate_y. easy. easy. apply ifthen_1_int. easy.
Qed.

Theorem ifthen_void1 : forall (k k1: nat), (k > 0) -> (k1 <> (k - 1)%nat) -> (k1 <> (k + 1)%nat) -> hoare_triple ({{((prob (x = k)) = (prob true)) /\ y1 = 0}}) (<{ x := x + 1 }>) 
                                                    (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R).
Proof. intros. apply HConseqLeft with (eta2 := tasgn_pt x <{ x + 1 }> (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold CTermexp_of_nat. unfold PTerm_of_R.
          intro.  replace (fst ps (fun st : state => ((x !-> ((fst st x) + 1)%nat; (fst st)) x) = (k1)%nat)) with (fst ps (fun st : state => ((fst st x) + 1)%nat = (k1)%nat)).
          destruct H2. rewrite H3. apply measure_P_eq_true in H2. symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> (fst st x))). intro. lia.
          apply H2. apply equivalence. intro. rewrite t_update_eq. lia.
        + apply HTAsgn.
Qed.

Theorem ifthen_void2 : forall (k k1: nat), (k > 0) -> (k1 <> (k - 1)%nat) -> (k1 <> (k+1)%nat) -> hoare_triple ({{((prob (x = k)) = (prob true)) /\ y2 = 0}}) (<{ x := x - 1 }>) 
                                                    (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R).
Proof. intros. apply HConseqLeft with (eta2 := tasgn_pt x <{ x - 1 }> (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> ((fst st x) - 1)%nat; (fst st)) x) = (k1)%nat)) with (fst ps (fun st : state => ((fst st x) - 1)%nat = k1)). unfold CTermexp_of_nat. unfold PTerm_of_R.
          intro. destruct H2. rewrite H3.  apply measure_P_eq_true in H2. symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> (fst st x))). intro. lia.
          apply H2. apply equivalence. intro. rewrite t_update_eq. lia.
        + apply HTAsgn.
Qed.

Theorem ifthen_void_int : forall (k k1: nat), (k > 0) -> (k1 <> (k - 1)%nat) -> (k1 <> (k+1)%nat) -> hoare_triple ({{((((prob (x = k /\ b )) = (prob b)) /\  ((prob (x = k /\~b )) = (prob ~b))) /\ y1 = 0) /\ y2 = 0}})
              (<{if b then x := x + 1 else x := x - 1 end}>)
              {{ y1 + y2 = (prob (x = (k1))) }}.
Proof. intros. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (x = k)) = (prob true)) /\ y1 = 0}}) ({{((prob (x = k)) = (prob true)) /\ y2 = 0}}) (b) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. replace (fst ps (fun st : state => True /\ (snd st b))) with (fst ps (fun st : state => (snd st b))).
        replace (fst ps (fun st : state => True /\ (~ (snd st b)))) with (fst ps (fun st : state => (~ (snd st b)))). 
         easy.
        apply equivalence. easy. apply equivalence. easy. 
      * apply HIfThen. 
        + uncoerce_basic. replace ((fun st : state => ((k1)%nat) = (fst st x))) with ((fun st : state => (fst st x) = ((k1)%nat))). apply ifthen_void1. easy. easy. easy.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + uncoerce_basic. replace (fun st : state => ((k1)%nat) = (fst st x)) with (fun st : state => (fst st x) = ((k1)%nat)). apply ifthen_void2. easy. easy. easy.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
Qed.

Theorem ifthen_void : forall (k k1: nat), (k > 0) -> (k1 <> (k - 1)%nat) -> (k1 <> (k+1)%nat) -> hoare_triple ({{(((prob (x = k /\ b )) = (prob b)) /\  ((prob (x = k /\~b )) = (prob ~b))) }})
              (<{if b then x := x + 1 else x := x - 1 end}>)
          {{0 = (prob (x = k1)) }}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob (x = k /\ b )) = (prob b)) /\  ((prob (x = k /\~b )) = (prob ~b))) }}) y1 0%R)
                          (eta3 := eta_update_y_p ({{0 + y1 = (prob (x = k1)) }}) y1 0%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite Rplus_0_l. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{(((prob (x = k /\ b )) = (prob b)) /\  ((prob (x = k /\~b )) = (prob ~b)) )/\ y1 = 0 }}) y2 0%R)
                                                            (eta3 := eta_update_y_p ({{ y1 + y2 = (prob (x = (k1))) }}) y2 0%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. lra. 
             easy.
          * apply eliminate_y. easy. easy. apply ifthen_void_int. easy. easy. easy.
Qed.

Theorem bodyvoid : forall (k k1: nat), (k > 0) -> (k1 <> (k - 1)%nat) -> (k1 <> (k+1)%nat) -> hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) 
<{ 
    b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
}>
                    {{0 = (prob (x = k1)) }}.
Proof. intros. apply HSeq with (eta2 := {{(prob (x = k)) = (prob true)}}).
        + apply HConseqLeft with (eta2 := btoss_pt b 0.25%R ({{(prob (x = k)) = (prob true)}})).
          * intro. uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl. replace (fst ps (fun st : state => k = (fst st x))) with (fst ps (fun st : state => (fst st x) = k)). lra.
            apply equivalence. easy.
          * apply HBToss.
        + apply HConseqLeft with (eta2 := ({{(((prob (x = k /\ b )) = (prob b)) /\  ((prob (x = k /\~b )) = (prob ~b))) }})).
          * uncoerce_basic. intro. intro. rewrite measure_true_dest with (Q := (fun st : state => (fst st x) = k)) in H2.
            symmetry in H2. replace (fst ps (fun st : state => k = (fst st x))) with (fst ps (fun st : state => (fst st x) = k)) in H2. apply Rplus_0_r_uniq in H2. split.
            - 
              transitivity (fst ps (fun st : state =>  snd st b /\ ~ ((fst st x) <> k))). apply equivalence. intro. unfold CBoolexp_of_bexp. unfold Beval. split. intro. split. easy. destruct H3. lia.
              split. lia. easy.   
              rewrite measure_AnotB. replace (fst ps (fun st : state => snd st b /\ ((fst st x) <> k))) with 0%R. unfold CBoolexp_of_bexp. unfold Beval. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H2. apply measure_inclusion. easy.
            - 
              transitivity (fst ps (fun st : state =>  ~ snd st b /\ ~ ((fst st x) <> k))). apply equivalence. intro. split.  intro. split. easy. lia.
              intro. split. lia. easy.  
              rewrite measure_AnotB. replace (fst ps (fun st : state => ~ snd st b /\ ((fst st x) <> k))) with 0%R. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H2. apply measure_inclusion. easy.
            - apply equivalence. easy.
          * apply ifthen_void. easy. easy. easy.
Qed.

Theorem body0 : forall (k : nat), 
  hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) 
<{ 
    b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
}>
                {{ 0.25 = (prob (x = (k + 1))) }}.
Proof. intros. apply HSeq with (eta2 := ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})).
        + apply HConseqLeft with (eta2 := btoss_pt b 0.25%R ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})).
          * intro. uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
            replace (fst ps (fun st : state => (k = (fst st x)) /\ ((b !-> True; (snd st)) b))) with (fst ps (fun st : state => (k = (fst st x)))).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ ((b !-> False; (snd st)) b))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ (~ ((b !-> True; (snd st)) b)))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ (~ ((b !-> False; (snd st)) b)))) with (fst ps (fun st : state => (k = (fst st x)))).
            replace (fst ps (fun st : state => (b !-> False; (snd st)) b)) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => ~ ((b !-> True; (snd st)) b))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (b !-> True; (snd st)) b)) with (fst ps (fun st : state => True)).
            replace (fst ps (fun st : state => ~ ((b !-> False; (snd st)) b))) with (fst ps (fun st : state => True)).
            rewrite empty_set_measure. rewrite Rmult_0_r. rewrite Rmult_0_r. rewrite Rplus_0_r. rewrite Rplus_0_l. replace (fst ps (fun st : state => k = (fst st x))) with (fst ps (fun st : state => (fst st x) = k)).
            lra. apply equivalence. intro. lia. 
            (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia).
            (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia).
          * apply HBToss.  
        + apply ifthen_0.
Qed. 

Theorem body1 : forall (k : nat), k > 0 ->
  hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) 
<{ 
    b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
}>
     (fun ps :Pstate => (0.75)%R = (fst ps (fun st : state => ((k - 1) = fst st x)%nat) )).
Proof. intros. apply HSeq with (eta2 := ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})).
       + apply HConseqLeft with (eta2 := btoss_pt b 0.25%R ({{(((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b) ) /\ ((prob (x = k /\ ~b)) = 0.75 /\ (prob (x = k /\ ~b)) = (prob ~b) )) }})).
          * intro. uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
            replace (fst ps (fun st : state => (k = (fst st x)) /\ ((b !-> True; (snd st)) b))) with (fst ps (fun st : state => (k = (fst st x)))).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ ((b !-> False; (snd st)) b))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ (~ ((b !-> True; (snd st)) b)))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (k = (fst st x)) /\ (~ ((b !-> False; (snd st)) b)))) with (fst ps (fun st : state => (k = (fst st x)))).
            replace (fst ps (fun st : state => (b !-> False; (snd st)) b)) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => ~ ((b !-> True; (snd st)) b))) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => (b !-> True; (snd st)) b)) with (fst ps (fun st : state => True)).
            replace (fst ps (fun st : state => ~ ((b !-> False; (snd st)) b))) with (fst ps (fun st : state => True)).
            rewrite empty_set_measure. rewrite Rmult_0_r. rewrite Rmult_0_r. rewrite Rplus_0_r. rewrite Rplus_0_l. replace (fst ps (fun st : state => k = (fst st x))) with (fst ps (fun st : state => (fst st x) = k)).
            lra. apply equivalence. intro. lia. 
            (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia).
            (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia). (apply equivalence; intro; rewrite t_update_eq; lia).
          * apply HBToss.  
        + apply ifthen_1. easy.
Qed. 
 

Fixpoint G_vector (n : nat) : (Vector.t Assertion n) :=
  match n with 
    | O => []%vector
    | S m => (CBoolexp_of_bexp (<{x = n}>) :: (G_vector m))%vector
end.

Fixpoint G_list (n : nat) : list Assertion :=
  match n with
    | O => []%list
    | S m => CBoolexp_of_bexp (<{x = n}>) :: (G_list m)
end.

Fixpoint T_vector (n : nat) : (Vector.t R n) :=
    match n with
      | O => []%vector  
      | S m => if (n =? 1) then ((0.75%R) :: T_vector m)%vector
                           else ((0%R) :: T_vector m)%vector
end.

Compute T_vector 3.

(* Fixpoint T_list (n : nat) : list R := 
  match n with
      | O => []%list  
      | S m => (((1 / (INR n + 1))%R) :: T_list m)%list
end. *)

Fixpoint P_vector_int (m i : nat) : Vector.t R m :=
  match m with 
    | O  => []%vector
    | S k =>  if (m =? (S i)) then ((0.25%R) :: P_vector_int k i)%vector
                              else (if ((S m) =? i) then ((0.75%R) :: P_vector_int k i)%vector
                                                    else ((0%R) :: P_vector_int k i)%vector)
end.

Compute P_vector_int 4 1.
(*  if (i =? 1) then (if (m =? i) then ((0.25%R) :: P_vector_int k i)%vector
                                            else ((0%R) :: P_vector_int k i)%vector)
              else ( *)

Fixpoint P_vector (n m : nat) : (Vector.t (Vector.t R m) n) :=
    match n with
     | O => []%vector
     | S k => ((P_vector_int m n) :: P_vector k m)%vector
end.

Compute P_vector 2 2.

Fixpoint X_vector_int (n i : nat) : Vector.t R i :=
    match i with 
      | O => []%vector
      | S k => ((1 - ( (3 ^ i - INR 1)/ (3 ^ n - INR 1)))%R :: (X_vector_int n k))%vector
end.

Definition X_vector (n : nat) : Vector.t R n := X_vector_int (n + 1) n.

Compute P_vector 2 2.
Compute P_vector 3 3.

Compute X_vector 3.


(* Definition G_vector (n : nat) : (Vector.t Assertion n) := vreverse (G_vector_r n).

Definition G_list (n : nat) : list Assertion := rev (G_list_r n). *)
Lemma helperGvec : forall (n : nat), to_list (G_vector (S n)) = CBoolexp_of_bexp (Eq (Const (S n)) (Var x)) :: to_list (G_vector n).
Proof. intro. unfold G_vector. unfold to_list. easy.
Qed.

Lemma helperGvec_int_true : forall (n i : nat), (i < n) -> PAImplies (nth i (to_list (Vector.map int_true_eq_one (G_vector n))) (fun ps : Pstate => True))
                                                                     (int_true_eq_one (CBoolexp_of_bexp (Eq (Const (n - i)) (Var x) ))).
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec i 0).
          * rewrite e. intro. simpl. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. uncoerce_basic.
            intro. split. transitivity (fst ps (fun st : state => (S n) = (fst st x))).
            apply equivalence. easy. easy. transitivity (fst ps (fun st : state => (S n) = (fst st x))). 
            apply equivalence. easy. easy.
          * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1.
                simpl. apply IHn. lia.
Qed.

Lemma helperXvec : forall (n i : nat), (to_list (X_vector_int n (S i))) = (1 - ( (3 ^ (S i) - INR 1)/ (3 ^ n - INR 1)))%R :: to_list (X_vector_int n i).
Proof. intro. unfold X_vector_int. unfold to_list. easy.
Qed.

Lemma helperXvec1_int : forall (n m i : nat), (i < m) -> nth i (to_list (X_vector_int n m)) 0%R = (1 - ( (3 ^ (m - i) - INR 1)/ (3^n - INR 1)))%R.
Proof. induction m. 
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec i 0).
          * rewrite e. reflexivity.
          * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. simpl. rewrite IHm. reflexivity. lia.
Qed.

Lemma helperXvec1 : forall (n i : nat), (i < n) -> nth i (to_list (X_vector n)) 0%R =   (1 - ( (3 ^ (n - i) - INR 1)/ (3 ^ (n + 1) - INR 1)))%R.
Proof. intros. unfold X_vector. rewrite helperXvec1_int. reflexivity. easy.
Qed.  

Lemma helperPvec1 : forall (n i m: nat), (i < n) -> (nth i (to_list (P_vector n m)) (const 0%R m)) = P_vector_int m (n - i).
Proof. induction n. intros.
        + assert (~ (i < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec i 0).
          * simpl. rewrite e. reflexivity. 
          * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. simpl. unfold to_list in IHn.
                 rewrite IHn. reflexivity. rewrite H1 in H. lia.
Qed.

Lemma helperVecSumi1 : forall (m n : nat),  (vector_sum (zip Rmult  (P_vector_int m 1) (X_vector_int n m))) = if (m <? 2) then 0%R else (0.25* (1 - ((3 ^ 2 - INR 1) / (3 ^ (n) - INR 1))))%R.
Proof. intros. induction m.
        + simpl. reflexivity.
        + simpl. destruct (Nat.eq_dec m 1).
          * rewrite e. simpl. rewrite Rmult_0_l. rewrite Rplus_0_r. rewrite Rplus_0_r.  lra.
          * replace (m =? 1) with (Datatypes.false). simpl. rewrite IHm. destruct (Nat.eq_dec m 0).
            ** replace (m <? 2) with (Datatypes.true). replace (S m <? 2) with (Datatypes.true). rewrite Rmult_0_l. rewrite Rplus_0_r. reflexivity. symmetry. apply Nat.ltb_lt. lia.
                symmetry. apply Nat.ltb_lt. lia.
            ** replace (m <? 2) with (Datatypes.false). replace (S m <? 2) with (Datatypes.false). rewrite Rmult_0_l. rewrite Rplus_0_l. rewrite INR_1. replace (3 * (3 * 1))%R with ((3 ^ 2))%R. reflexivity. lra.
               symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.ltb_nlt. lia. 
            ** symmetry. apply Nat.eqb_neq.  lia. 
Qed. 

Lemma helperVecSum : forall (m n i : nat), i > 1 -> (vector_sum (zip Rmult  (P_vector_int m i) (X_vector_int n m))) = if (S m <? i) then (0%R) else 
                                                                                                                                          (if (m <? S i) then (0.75*(1 - ((3 ^ (i - 1) - INR 1) / (3 ^ n - INR 1))))%R
                                                                                                                                                         else ((0.75*(1 - ((3 ^ (i - 1) - INR 1) / (3 ^ n - INR 1))))%R + (0.25*(1 - ((3 ^ (i + 1) - INR 1) / (3 ^ n - INR 1))))%R)%R).
Proof. intros m n i H. induction m.
        + simpl. replace (1 <? i) with (Datatypes.true). easy. symmetry. apply ltb_lt. easy.
        + destruct (Nat.eq_dec (S (S m)) i).
          * unfold P_vector_int. replace ((S m) =? S i) with Datatypes.false. replace ((S (S m)) =? i) with Datatypes.true.
            simpl. unfold P_vector_int in IHm. simpl in IHm. rewrite IHm. replace ((S m) <? i) with Datatypes.true.
            replace ((S m) <? (S i)) with Datatypes.true. replace ((S (S m)) <? i) with Datatypes.false.
            replace ((3 ^ (i - 1)) - 1)%R with ((3 * (3 ^ m)) - 1)%R. rewrite Rplus_0_r. reflexivity.
            replace (i - 1) with (S m)%nat. Search (pow _ (S _)). rewrite tech_pow_Rmult. easy. lia. 
            symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.ltb_lt. lia. symmetry. apply Nat.ltb_lt. lia. symmetry. apply Nat.eqb_eq. lia. symmetry. apply Nat.eqb_neq. lia.
          * destruct (Nat.eq_dec (S m) (S i)).
            ** unfold P_vector_int. replace ((S m) =? (S i)) with Datatypes.true. simpl. unfold P_vector_int in IHm. simpl in IHm. rewrite IHm.
               replace (S m <? i) with Datatypes.false. replace (m <? S i) with Datatypes.true. replace ((S m) <? (S i)) with Datatypes.false. replace (S (S m) <? i) with Datatypes.false.
               rewrite Rplus_comm. replace ((3 ^ (i + 1)) - 1)%R with ((3 * (3 ^ m)) - 1)%R. reflexivity. rewrite tech_pow_Rmult. replace (S m) with (i + 1)%nat. easy.
                lia. symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.ltb_lt. lia. symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.eqb_eq. lia.
            ** unfold P_vector_int. replace ((S m) =? S i) with Datatypes.false. replace ((S (S m)) =? i) with Datatypes.false.
                simpl. unfold P_vector_int in IHm. simpl in IHm. rewrite IHm. rewrite Rmult_0_l. rewrite Rplus_0_l.
                Search "dec" in Nat. Search "dec" in Bool. destruct (bool_dec ((S m) <? i) Datatypes.true).
                  -  rewrite e. replace ((S (S m)) <? i) with (Datatypes.true). reflexivity. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in e. lia.
                  - replace ((S m) <? i) with Datatypes.false. replace ((S (S m)) <? i) with (Datatypes.false). apply not_true_is_false in n2. apply Nat.ltb_nlt in n2.
                          destruct (bool_dec (m <? S i) Datatypes.true).
                          -- rewrite e. replace ((S m) <? (S i)) with Datatypes.true. reflexivity. symmetry. apply Nat.ltb_lt. apply Nat.ltb_lt in e. lia.
                          -- apply not_true_is_false in n3. apply Nat.ltb_nlt in n3. replace (m <? S i) with Datatypes.false. replace ((S m) <? (S i)) with Datatypes.false. reflexivity. symmetry. apply Nat.ltb_nlt. lia.
                             symmetry. apply Nat.ltb_nlt. lia. 
                          -- symmetry. apply Nat.ltb_nlt. apply not_true_is_false in n2. apply Nat.ltb_nlt in n2. lia.
                          -- symmetry. apply Nat.ltb_nlt. apply not_true_is_false in n2. apply Nat.ltb_nlt in n2. lia.
                  - symmetry. apply Nat.eqb_neq. lia.
                  - symmetry. apply Nat.eqb_neq. lia.
Qed.

(* Lemma helperVecSum_int1 : forall (n i : nat), (i > 0) -> (i <= n) -> (vector_sum (zip Rmult  (P_vector_int n (S i)) (X_vector n))) = ((1 - (1/ INR (S i)))*(1 - (INR (S i))/(INR n + 1)))%R.
Proof. intros. unfold X_vector. rewrite helperVecSum. destruct (Nat.eq_dec n i).
        + rewrite e. replace (i <? (S i)) with (Datatypes.true). Search INR. rewrite S_INR. field. rewrite <- S_INR. Search INR. rewrite <- INR_0. apply not_INR. lia.
          symmetry. rewrite ltb_lt. lia. 
        + replace ( n <? S i ) with (Datatypes.false). easy. symmetry. rewrite ltb_nlt. lia.
        + lia.
Qed.  *)



(* (vector_sum (zip Rmult (nth i (to_list (P_vector n n)) (const 0 n)) (X_vector n))) *)

Lemma helper0 : forall (n : nat), G_list n = Vector.to_list (G_vector n).
Proof. induction n.
      + simpl. easy.
      + simpl. unfold G_list. unfold G_vector. simpl. unfold G_list in IHn. rewrite IHn. unfold to_list. simpl. reflexivity.
Qed.  

Lemma helper00: forall (n i : nat), (i < n) -> Assertion_equiv (List.nth i (to_list (G_vector n)) (fun st => True)) (CBoolexp_of_bexp (Eq (Var x) (sub (Const n) (Const i)))).
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intro i. destruct (Nat.eq_dec i 0).
          * intro. intro. rewrite e. simpl. lia.
          * intro. intro. rewrite <- helper0. rewrite <- helper0 in IHn. unfold to_list. simpl. 
            assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. apply IHn. lia.
Qed.

Lemma helperTvec : forall (n i : nat), (i < n) -> (List.nth i (to_list (T_vector n)) (0%R)) = if (n =? i + 1) then 0.75%R else 0%R.
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intro i. destruct (Nat.eq_dec i 0).
          * rewrite e. intro. simpl. destruct (Nat.eq_dec n 0).
            ** replace (n =? 0) with Datatypes.true. replace ((n -0 )=? 0) with Datatypes.true. reflexivity.
                symmetry. apply Nat.eqb_eq. lia. symmetry. apply Nat.eqb_eq. lia.
            ** replace (n =? 0) with Datatypes.false. replace ((n -0 )=? 0) with Datatypes.false. reflexivity.
                symmetry. apply Nat.eqb_neq. lia. symmetry. apply Nat.eqb_neq. lia.
          * intro. unfold to_list. simpl. 
            assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0.  unfold to_list in IHn. rewrite H1. 
                destruct (Nat.eq_dec n 0). 
                ** replace (n =? 0) with Datatypes.true. simpl. apply IHn. lia. symmetry. apply Nat.eqb_eq. lia.
                ** replace (n =? 0) with Datatypes.false. simpl. apply IHn. lia. symmetry. apply Nat.eqb_neq. lia.
Qed. 


Lemma helper1 : forall (n i : nat), (i < n) -> (forall st : state, (List.nth i (to_list (G_vector n)) (fun st : state => True) st) -> (Beval (Leq (Const 1) (Var x)) st)).
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intro i. destruct (Nat.eq_dec i 0).
          * intro. intro. rewrite e. simpl. lia.
          * intro. intro. rewrite <- helper0. rewrite <- helper0 in IHn. unfold to_list. simpl. 
            assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. apply IHn. lia.
Qed.

(* Lemma helper2_int : forall (i n : nat), (i < n) -> (forall st : state,
  ~ ((nth i (to_list (G_vector n)) (fun st1:state => True) st) /\ (CBoolexp_of_bexp ((Eq (Var x) (Const (S n)))) st) )).
Proof. intros. replace (nth i (to_list (G_vector n)) (fun st => True) st) with ((CBoolexp_of_bexp (Eq (Var x) (sub (Const n) (Const i)))) st). uncoerce_basic. lia.
       apply propositional_extensionality. symmetry. apply helper00. apply H.
Qed. *) 

Lemma helper2: forall i j n: nat,
(i < n) ->
((j < i) ->
 (forall st : state,
  ~ ((nth i (to_list (G_vector n)) (fun st1:state => True) st) /\ (nth j (to_list (G_vector n)) (fun st1 : state => True) st)))).
Proof. intros. replace (nth i (to_list (G_vector n)) (fun st => True) st) with ((CBoolexp_of_bexp (Eq (Var x) (sub (Const n) (Const i)))) st). 
        replace (nth j (to_list (G_vector n)) (fun st => True) st) with ((CBoolexp_of_bexp (Eq (Var x) (sub (Const n) (Const j)))) st).
        uncoerce_basic. lia. apply propositional_extensionality. symmetry. apply helper00. apply lt_trans with (m := i). easy. easy.
        apply propositional_extensionality. symmetry. apply helper00. easy.
Qed.

Lemma helperPvec2 : forall (m i j: nat), (j < m) -> (nth j (to_list (P_vector_int m i)) 0%R) = if ((m - j) =? (S i)) then (0.25%R)
                                                                                                                else (if ((S (m - j)) =? i) then (0.75%R)
                                                                                                                      else (0%R) ).
Proof. induction m. 
        + intros. assert (~ (j < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec j 0).
          * rewrite e. simpl. destruct (bool_dec (m =? i) Datatypes.true). rewrite e0. simpl. reflexivity.
             apply not_true_is_false in n.
            rewrite n.  destruct (bool_dec (S (S m) =? i) Datatypes.true). replace i with (S (S m)). replace (m =? m) with Datatypes.true.
            simpl. reflexivity. symmetry. apply Nat.eqb_eq. lia. apply Nat.eqb_eq in e0. easy. replace (match i with
          | S (S m'0) => m =? m'0
          | _ => Datatypes.false
          end) with (Datatypes.false). easy. destruct i. easy. destruct i. easy. apply not_true_is_false in n0. symmetry. apply Nat.eqb_neq. apply Nat.eqb_neq in n0. lia.
           * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, j = (S k1)). apply T. apply n. inversion H0. rewrite H1.  simpl.
                destruct (bool_dec (m =? i) Datatypes.true). rewrite e. simpl. unfold to_list in IHm. rewrite IHm.
                replace  (match i with
         | 0 => Datatypes.false
         | S m' => (m - x0) =? m'
         end) with ((S (m - x0)) =? i). reflexivity. destruct i. apply Nat.eqb_neq. apply Nat.eqb_eq in e. lia. 
          destruct (bool_dec ((m - x0) =? i) Datatypes.true). replace ((S (m - x0)) =? (S i)) with Datatypes.true. easy. replace ((S (m - x0)) =? (S i)) with Datatypes.false. apply not_true_is_false in n0. easy.
          apply not_true_is_false in n0. easy. lia. apply not_true_is_false in n0. rewrite n0. destruct (bool_dec (S (S m) =? i) Datatypes.true). replace i with (S (S m)). replace (m =? m) with Datatypes.true.
          simpl. apply IHm. lia. symmetry. apply Nat.eqb_eq. lia. apply Nat.eqb_eq in e. easy. replace (match i with
          | S (S m'0) => m =? m'0
          | _ => Datatypes.false
          end) with (Datatypes.false). simpl. apply IHm. lia. destruct i. reflexivity. destruct i. reflexivity. symmetry. apply Nat.eqb_neq. apply not_true_is_false in n1. apply Nat.eqb_neq in n1. lia.
Qed. 

Lemma helperPvec3 : forall (m i : nat), (1 < i) -> (i <= m) -> (nth (S (m - i)) (to_list (P_vector_int m i)) 0%R) = 0.75%R.
Proof. intros. rewrite helperPvec2. replace ((m - (S (m - i))) =? (S i)) with Datatypes.false. replace ((S (m - (S (m - i)))) =? i) with Datatypes.true. easy.
        symmetry. apply Nat.eqb_eq. lia. symmetry. apply Nat.eqb_neq. lia. lia.
Qed.

Lemma helper3 : forall (i n : nat), (i < n) ->  ((List.nth i (to_list (T_vector n)) (0%R)) > 0)%R \/ (exists (j : nat), (n > j) /\ (j > i) /\ ((List.nth j (Vector.to_list (List.nth i (Vector.to_list (P_vector n n)) (const 0%R n))) 0%R) > 0)%R).
Proof. intros. rewrite helperPvec1. destruct (Nat.eq_dec i (n - 1)).
        + left. rewrite e. rewrite helperTvec. replace (n =? ((n - 1) + 1)) with Datatypes.true. lra. symmetry. apply Nat.eqb_eq. lia. lia.
        + right. exists (i + 1)%nat. split. lia. split. lia. replace (i + 1)%nat with (S (n - (n - i))). rewrite helperPvec3. lra. lia. lia. lia. 
        + easy. 
Qed. 

Lemma helper4 : forall (n m: nat), (n > 0) -> hoare_triple (int_true_eq_one (CBoolexp_of_bexp (<{x = n}>)))
      <{ 
    b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
}>
      (inner_conj_geq (G_vector m) (P_vector_int m ( n))).
Proof. intro. induction m. 
        + intro. simpl. unfold inner_conj_geq. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip.
          unfold PAssertion_conj. unfold int_true_eq_one. uncoerce_basic. apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3 := {{ 0.25 = (prob (x = (n + 1))) }}).
          * intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (fst st x) = n)) with (fst ps (fun st : state => n = (fst st x))).
           easy. apply equivalence. easy.
          * easy.
          * apply body0. 
        + intro. simpl. destruct (Nat.eq_dec m n).
          * replace (m =? n) with (Datatypes.true). unfold inner_conj_geq. unfold PAssertion_conj. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip. simpl. intros. apply HAnd.
            -- rewrite e. assert (T: forall (k : nat), k > 0 -> exists k1, k = (S k1)). 
                - intro. destruct k. lia. intro. exists k. reflexivity.
                - assert (exists k1 : nat, n = (S k1)). apply T. apply H. inversion H0. rewrite H1. unfold gamma_geq. unfold gamma_compare. 
                  apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3  := {{ 0.25 = (prob (x = (n + 1))) }}).
                  ** intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (S x0) = (fst st x))) with (fst ps (fun st : state => (fst st x) = (n))). easy.
                     apply equivalence. intro. lia.
                  ** intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (S (S x0)) = (fst st x))) with (fst ps (fun st : state => ((n + 1)%nat) = (fst st x))). lra.
                      apply equivalence. intro. lia.  
                  ** uncoerce_basic. apply body0.  
            -- apply IHm. easy. 
            -- symmetry. apply Nat.eqb_eq. easy.
          * replace (m =? n) with (Datatypes.false). unfold inner_conj_geq. unfold PAssertion_conj. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip. simpl. apply HAnd.
            -- destruct (Nat.eq_dec n (S (S m))). rewrite e. replace (m =? m) with Datatypes.true. simpl. apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3 := (fun ps :Pstate => (0.75)%R = (fst ps (fun st : state => ((n - 1) = fst st x)%nat) ))).
                ** intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (S (S m)) = (fst st x))) with (fst ps (fun st : state => (fst st x) = n)).
                   easy. apply equivalence. intro. lia.
                **  intro. unfold gamma_geq. unfold gamma_compare. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. intro. apply Req_ge. symmetry.  transitivity (fst ps (fun st : state => (n - 1) = (fst st x))).
                    easy. apply equivalence. intro. lia.
                **  uncoerce_basic. apply body1. easy. 
                ** symmetry. apply Nat.eqb_eq. lia.
                ** replace (match n with
            | S (S m'0) => m =? m'0
            | _ => Datatypes.false
            end) with Datatypes.false. simpl. apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3 := {{0 = (prob (x = (m + 1))) }}).
                  ++ intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (fst st x) = n)) with (fst ps (fun st : state => n = (fst st x))).
                      easy. apply equivalence. intro. lia.
                  ++ intro. unfold gamma_geq. unfold gamma_compare. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => ((m + 1)%nat) = (fst st x))) with (fst ps (fun st : state => (S m) = (fst st x))).
                      lra. apply equivalence. intro. lia.
                  ++ uncoerce_basic. apply bodyvoid with (k := n) (k1 := ( m + 1)%nat). lia. lia. lia.
                  ++ destruct n. reflexivity. destruct n. reflexivity. symmetry. apply Nat.eqb_neq. lia. 
            -- replace (Vector.tl
           (if match n with
               | S (S m'0) => m =? m'0
               | _ => Datatypes.false
               end
            then ((0.75%R) :: (P_vector_int m n))%vector
            else ((0%R) :: (P_vector_int m n))%vector)) with (P_vector_int m n). apply IHm. easy. destruct (Nat.eq_dec n (S (S m))).
                  rewrite e. replace (m =? m) with Datatypes.true. easy. symmetry. apply Nat.eqb_eq. lia.
                  destruct n. easy. destruct n. easy. replace (m =? n) with Datatypes.false. easy. symmetry. apply Nat.eqb_neq. lia.
            -- symmetry. apply Nat.eqb_neq. easy.
Qed.

Lemma helper5 : forall (n : nat), (n > 0) -> Assertion_equiv (nth (n - 1) (to_list (G_vector n)) {{true}}) (CBoolexp_of_bexp ((Eq (Const 1) (Var x)))).
Proof. intro. induction n.
        + intro. assert (~ (0 < 0)). lia. contradiction. 
        + intro. rewrite helperGvec. unfold nth. destruct (Nat.eq_dec ((S n) - 1) 0). 
            * replace ((S n)-1) with 0. assert (S n = 1). lia. rewrite H0. easy.  
            * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, (S n) - 1 = (S k1)). apply T. apply n0. inversion H0. rewrite H1.
                unfold nth in IHn. replace x0 with (n - 1). apply IHn. lia. lia.
Qed.

Lemma helper6_int : forall (n i : nat), (i > 0) -> (nth (i - 1) (Vector.to_list (X_vector_int n i)) 0%R) = (1 - ((3 - INR 1) / (3 ^ n - 1)))%R.
Proof. intro. induction i.
        + assert (~ (0 < 0)). lia. contradiction.
        + intro. rewrite helperXvec. unfold nth. destruct (Nat.eq_dec ((S i) - 1) 0).
            * replace ((S i)-1) with 0. assert (S i = 1). lia. rewrite H0. Search (_ ^ 1). replace (3 ^ 1)%R with 3%R. easy. lra.   
            * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, (S i) - 1 = (S k1)). apply T. apply n0. inversion H0. rewrite H1.
                unfold nth in IHi. replace x0 with (i - 1). apply IHi. lia. lia.
Qed.

Lemma helper6 : forall (n : nat), (n > 0) -> (nth (n - 1) (Vector.to_list (X_vector n)) 0%R) = ((1 + (- (2 / ((3 ^ (n + 1)) - 1))))%R).
Proof. unfold X_vector. intros. transitivity (1 - ((3 - INR 1) / (3 ^ (n+1) - 1)))%R. rewrite helper6_int. reflexivity. easy.
        replace (3 - (INR 1))%R with 2%R. lra. rewrite INR_1. lra. 
Qed.    
           
(* 
Lemma helper5 : forall (i n m : nat), (n > 0) -> (i < n) -> hoare_triple (nth i (to_list (Vector.map int_true_eq_one (G_vector n))) (fun ps => True)) 
(CSeq (uniform_xplus1) <{if val = 0 then x := 0 else x := (x + 1) end}>)
(nth i
     (to_list
        (antecedent_geq (G_vector n) (P_vector n m) (Leq (Const 1) (Var x)) (fun st : state => (fst st x) = 0)
           (T_vector n))) (fun ps => True)). *)

(* Lemma helper5 : forall (i n : nat), (n > 0) -> (i < n) -> 
    PAImplies (fun ps : Pstate => (inner_conj_geq (G_vector n) (P_vector_int n (S (n - i))) ps) /\ ((fst ps (fun st : state => (~ ((1 <= (fst st x))%nat)) /\ ((fst st x) = (0%nat)))) >= 1/(INR (S (n - i))))%R) 
              (nth i
                (to_list
                  (antecedent_geq (G_vector n) (P_vector n n) (Leq (Const 1) (Var x)) (fun st : state => (fst st x) = 0)
                      (T_vector n))) (fun ps => True)).
Proof. intros. intro. induction i.
          + unfold antecedent_geq. unfold gamma_geq. unfold inner_conj_geq. unfold gamma_compare. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold gamma_geq.
              unfold gamma_compare. repeat (
    unfold CTermexp_of_nat;
    unfold CTermexp_of_Texp;
    unfold PTerm_of_R; unfold PTermexp_of_pterm; unfold Pteval; unfold CBoolexp_of_bexp; unfold Beval; unfold Teval
    ). simpl. 
        assert (T: forall (k : nat), k > 0 -> exists k1, k = (S k1)). 
                - intro. destruct k. lia. intro. exists k. reflexivity.
                - assert (exists k1 : nat, n = (S k1)). apply T. apply H. inversion H1. rewrite H2. simpl. replace (x0 =? (S x0)) with (Datatypes.false). replace (x0 =? (x0 + 1)) with (Datatypes.false).
                  simpl. intro. split. simpl. replace (S (x0 + 1)) with (S (S x0)). easy.
                  lia. easy. symmetry. apply Nat.eqb_neq. lia. symmetry. apply Nat.eqb_neq. lia.
          + unfold antecedent_geq. unfold gamma_geq. unfold inner_conj_geq. unfold gamma_compare. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold gamma_geq.
              unfold gamma_compare. repeat (
    unfold CTermexp_of_nat;
    unfold CTermexp_of_Texp;
    unfold PTerm_of_R; unfold PTermexp_of_pterm; unfold Pteval; unfold CBoolexp_of_bexp; unfold Beval; unfold Teval
    ). simpl. unfold nth. unfold to_list. simpl. unfold Vector.hd. easy. unfold apply_func. simpl. easy.  intro.
                  split. destruct H3. apply H3. easy. easy. split.
                  easy.
                  easy. *)


(* Lemma helper5: forall (i n : nat), (i < n) -> 
hoare_triple (nth i (to_list (Vector.map int_true_eq_one (G_vector n))) (fun ps => True)) 
(CSeq (uniform_xplus1) <{if val = 0 then x := 0 else x := (x + 1) end}>)
(nth i
     (to_list
        (antecedent_geq (G_vector n) (P_vector n n) (Leq (Const 1) (Var x)) (fun st : state => (fst st x) = 0)
           (T_vector n))) (fun ps => True)).
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intro. destruct (Nat.eq_dec i 0).
          * rewrite e. unfold antecedent_geq. unfold gamma_geq. unfold inner_conj_geq. unfold gamma_compare. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold gamma_geq.
              unfold gamma_compare. repeat (
    unfold CTermexp_of_nat;
    unfold CTermexp_of_Texp;
    unfold PTerm_of_R; unfold PTermexp_of_pterm; unfold Pteval; unfold CBoolexp_of_bexp; unfold Beval; unfold Teval
    ). simpl. 
    unfold antecedent_geq in IHn. unfold gamma_geq in IHn. unfold inner_conj_geq in IHn. unfold gamma_compare in IHn. unfold zip_gamma_geq in IHn. unfold zip_gamma_compare in IHn. unfold gamma_geq in IHn.
              unfold gamma_compare in IHn. repeat (
    unfold CTermexp_of_nat in IHn;
    unfold CTermexp_of_Texp in IHn;
    unfold PTerm_of_R in IHn; unfold PTermexp_of_pterm in IHn; unfold Pteval in IHn; unfold CBoolexp_of_bexp in IHn; unfold Beval in IHn; unfold Teval in IHn
    ). simpl in IHn. unfold apply_func. apply HAnd. apply HAnd. replace (n =? (n+1)) with (Datatypes.false). simpl. admit.
        admit. replace (n =? (n+1)) with (Datatypes.false). simpl. unfold PAssertion_conj. unfold Vector.hd. unfold zip. unfold nth. simpl.
             unfold PAssertion_conj. simpl. lia.
          * intro. intro. rewrite <- helper0. rewrite <- helper0 in IHn. unfold to_list. simpl. 
            assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. apply IHn. lia.
Qed. *)


Theorem Rwalk_term_int : forall (n : nat) (beta : bexp) (tempA : Assertion), (n >0) -> (beta = (Leq (Const 1) (Var x))) -> Assertion_equiv tempA (CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) -> 
        hoare_triple ({{(prob (beta /\ tempA)) >= y1 /\ (prob (beta /\ tempA)) = (prob true)}}) 

  (While beta
   (<{ b toss 0.25;
    if b then x := x + 1 else x := x - 1 end
}>))
 (fun ps : Pstate => ((1 - (2 /(3^ (n + 1) - 1)))*(snd ps y1) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R).
Proof. intros. eapply HWhileLB3 with (m := n) (G := G_vector n) (T := T_vector n) (P := P_vector n n) (X := X_vector n) (i := n - 1).
        + rewrite H0. apply helper1.
        + intros. apply helper2. easy. easy.
        + intro. intro. apply helper3. easy.
        + unfold antgeq2. intros. apply HAnd. apply HConseqLeft with (eta2 := (int_true_eq_one (CBoolexp_of_bexp (Eq (Const (n - i)) (Var x) )))).
          * apply helperGvec_int_true. easy.
          * rewrite helperPvec1 with (n := n) (m := n). apply helper4. lia. lia.
          * rewrite helperTvec. unfold gamma_geq. apply HConseqLeft with (eta2 := (int_true_eq_one (CBoolexp_of_bexp (Eq (Const (n - i)) (Var x) )))).
            - apply helperGvec_int_true. easy.
            - unfold gamma_compare. uncoerce_basic. destruct (Nat.eq_dec n (i + 1)).
              ** replace (n =? (i + 1)) with Datatypes.true.  apply HConseq with (eta2 := ((fun st : Pstate =>
   and
     (((fun st0 : Pstate =>
        eq
          (((fun st1 : Pstate =>
             Pteval
               (Pint
                  (fun st2 : state =>
                   eq ((CTermexp_of_Texp (Var x) : CTermexp) st2)
                     ((CTermexp_of_nat (n - i) : CTermexp) st2))) st1)
            :
            PTermexp) st0) ((PTerm_of_R 1 : PTermexp) st0))
       :
       PAssertion) st)
     (((fun st0 : Pstate =>
        eq
          (((fun st1 : Pstate =>
             Pteval
               (Pint
                  (fun st2 : state =>
                   eq ((CTermexp_of_Texp (Var x) : CTermexp) st2)
                     ((CTermexp_of_nat (n - i) : CTermexp) st2))) st1)
            :
            PTermexp) st0)
          (((fun st1 : Pstate => Pteval (Pint (fun _ : state => True)) st1) : PTermexp) st0))
       :
       PAssertion) st)))) (eta3 := (fun ps :Pstate => (0.75)%R = (fst ps (fun st : state => (0 = fst st x)%nat) ))). 
              -- intro. unfold int_true_eq_one.  uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. 
                  replace (fst ps (fun st2 : state => (fst st2 x) = (n - i))) with (fst ps (fun st : state => (n - i) = (fst st x))). easy. apply equivalence. intro. lia. 
              -- intro. intro. replace (fst ps (fun st : state => (~ (CBoolexp_of_bexp beta st)) /\ ((fst st x) = (0%nat)))) with (fst ps (fun st : state => 0 = (fst st x))).
                 rewrite <- H3. lra. apply equivalence. intro. unfold CBoolexp_of_bexp. rewrite H0. unfold Beval. unfold Teval. lia.
              -- uncoerce_basic. apply HConseqLeft with (eta2 := (fun st : Pstate =>
   ((fst st (fun st2 : state => (fst st2 x) = 1)) = (1%R)) /\
   ((fst st (fun st2 : state => (fst st2 x) = 1)) = (fst st {{true}})))). intro. replace (fst ps (fun st2 : state => (fst st2 x) = (n - i))) with (fst ps (fun st2 : state => (fst st2 x) = 1%nat)).
                  easy. apply equivalence. intro. lia. apply body1 with (k := 1). lia.
              -- symmetry. apply Nat.eqb_eq. lia.
             ** replace (n =? (i + 1)) with Datatypes.false. apply HConseq with (eta2 := ((fun st : Pstate =>
   and
     (((fun st0 : Pstate =>
        eq
          (((fun st1 : Pstate =>
             Pteval
               (Pint
                  (fun st2 : state =>
                   eq ((CTermexp_of_Texp (Var x) : CTermexp) st2)
                     ((CTermexp_of_nat (n - i) : CTermexp) st2))) st1)
            :
            PTermexp) st0) ((PTerm_of_R 1 : PTermexp) st0))
       :
       PAssertion) st)
     (((fun st0 : Pstate =>
        eq
          (((fun st1 : Pstate =>
             Pteval
               (Pint
                  (fun st2 : state =>
                   eq ((CTermexp_of_Texp (Var x) : CTermexp) st2)
                     ((CTermexp_of_nat (n - i) : CTermexp) st2))) st1)
            :
            PTermexp) st0)
          (((fun st1 : Pstate => Pteval (Pint (fun _ : state => True)) st1) : PTermexp) st0))
       :
       PAssertion) st)))) (eta3 := {{0 = (prob (x = 0)) }}).
              -- intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval.
                  replace (fst ps (fun st2 : state => (fst st2 x) = (n - i))) with (fst ps (fun st : state => (n - i) = (fst st x))). easy. apply equivalence. intro. lia.
              -- intro. uncoerce_basic. unfold CBoolexp_of_bexp. rewrite H0. unfold Beval. unfold Teval. intro. apply Req_ge. transitivity  (fst ps (fun st : state => 0 = (fst st x))).
                  apply equivalence. intro. lia. easy.
              -- apply bodyvoid. lia. lia. lia.
              -- symmetry. apply Nat.eqb_neq. lia.
            - easy. 
        + intros. unfold lin_ineq_lb. simpl. rewrite helperPvec1. 
              unfold X_vector.  destruct (Nat.eq_dec (n - i) 1).
            - rewrite e. unfold X_vector. rewrite helperVecSumi1. rewrite helperTvec. rewrite helperXvec1. apply Req_le.
              replace (n =? (i + 1)) with Datatypes.true. rewrite e. admit. symmetry. apply Nat.eqb_eq. lia. easy. easy.
            - rewrite helperVecSum. rewrite helperXvec1. destruct (Nat.eq_dec (n - i) n).
              ** replace i with 0. replace (S n <? (n - 0)) with Datatypes.false. replace (n <? S (n - 0)) with Datatypes.true. rewrite helperTvec. replace (n =? (0 + 1)) with Datatypes.false. admit. 
                  symmetry. apply Nat.eqb_neq. lia. easy. symmetry. apply Nat.ltb_lt. lia. symmetry. apply Nat.ltb_nlt. lia.  lia. 
              ** unfold X_vector. replace ((S n) <? (n - i)) with Datatypes.false.
              replace (n <? (S (n - i))) with Datatypes.false. rewrite helperTvec. replace (n =? (i + 1)) with Datatypes.false. admit.
              symmetry. apply Nat.eqb_neq. lia. easy. symmetry. apply Nat.ltb_nlt. lia. symmetry. apply Nat.ltb_nlt. lia.
              ** easy.
              ** lia.  
            - easy.
        + lia. 
        + intros. Search "iff" in Logic. apply iff_trans with ( B:= ((CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) st)). apply helper5. easy. easy.
        + rewrite helper6. lra. easy. 
Admitted.

(* Theorem Espline_term_y : forall (n : nat), (n > 0) -> hoare_triple ({{(prob (x = 1)) >= y1 /\ (prob (x = 1)) = (prob true)}}) 
      (While (Leq (Const 1) (Var x)) (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>)) )
 (fun ps : Pstate => ((1 - (1/(INR n + 1)))*(snd ps y1) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R).
Proof. intros. apply HConseqLeft with (eta2 := (fun st : Pstate =>
     (((PTermexp_of_pterm (Pvar y1) st) <=
       (Pteval (Pint (fun st0 : state => (CBoolexp_of_bexp (Leq (Const 1) (Var x)) st0) /\ ((CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) st0))) st))%R) /\
     ((Pteval (Pint (fun st0 : state => (CBoolexp_of_bexp (Leq (Const 1) (Var x)) st0) /\ ((CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) st0))) st) =
      (Pteval (Pint {{true}}) st)))). intro. uncoerce_basic. 
        replace (fst ps (fun st0 : state => ((1 <= (fst st0 x))%nat) /\ ((1%nat) = (fst st0 x)))) with (fst ps (fun st : state => (1%nat) = (fst st x))). 
         easy. apply equivalence. intro. lia. apply Espline_term_int. easy. easy. easy.
Qed.

Theorem Espline_term_elim_y : forall (n : nat), (n > 0) ->  hoare_triple ({{(prob (x = 1)) >= 1 /\ (prob (x = 1)) = (prob true)}}) 
      (While (Leq (Const 1) (Var x)) (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>)) )
 (fun ps : Pstate => ((1 - (1/(INR n + 1))) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R).
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(prob (x = 1)) >= y1 /\ (prob (x = 1)) = (prob true)}}) y1 1%R) (eta3 := eta_update_y_p (fun ps : Pstate => ((1 - (1/(INR n + 1)))*(snd ps y1) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R) y1 1%R).
          + intro. uncoerce_basic. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. intro. simpl. rewrite t_update_eq. easy.
          + intro. uncoerce_basic. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. simpl. rewrite t_update_eq. rewrite Rmult_1_r. easy.
          + apply eliminate_y. easy. easy. apply HConseqLeft with (eta2 := ({{(prob (x = 1)) >= y1 /\ (prob (x = 1)) = (prob true)}})).
            * intro. uncoerce_basic. easy.
            * apply Espline_term_y. easy.
Qed.

Theorem Espline_term : forall (n : nat), (n > 0) -> hoare_triple ({{(prob true) = 1}}) (Escaping_spline) (fun ps : Pstate => ((1 - (1/(INR n + 1))) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R).
Proof. intros. apply HSeq with (eta2 := ({{(prob (x = 1)) = 1 /\ (prob (x = 1)) = (prob true)}})).
        + apply HConseqLeft with (eta2 := tasgn_pt x 1 ({{(prob (x = 1)) = 1 /\ (prob (x = 1)) = (prob true)}})).
          * intro. uncoerce_basic. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. unfold Teval.
            simpl. replace (fst ps (fun st : state => 1 = ((x !-> 1; (fst st)) x))) with (fst ps {{true}}). easy. apply equivalence. intro. rewrite t_update_eq. lia.
          * apply HTAsgn.
        + apply HConseqLeft with (eta2 := ({{(prob (x = 1)) >= 1 /\ (prob (x = 1)) = (prob true)}})).
          * intro. uncoerce_basic. lra.
          * apply Espline_term_elim_y. easy.
Qed. *)
