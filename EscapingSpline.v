Print Libraries.
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
Definition ct : string := "ct".

Definition uniform_xplus1 : Cmd := 
  CSeq (<{ ct := 0 }> ) (While (<{ ct <= x }>) (CSeq (body) (<{ (ct := ct + 1) }>))).

Definition test (k : nat) : R := (1 - (1/ INR k + 1)).
Check PTerm_of_R (test 1).
Definition one_third : R := (1/(INR 3 + 1))%R.


Axiom uniform : forall (k : nat), 
  hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (uniform_xplus1)
                                    (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => ((fst st x = k) /\ ((fst st) val) = 0%nat)))%R)).

Axiom uniform_neg : forall (k : nat), hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (uniform_xplus1)
                                    (fun ps : Pstate => ((1-(1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ ((fst st) val) <> 0%nat))%R)).

Axiom x_inv : forall (k : nat), hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (uniform_xplus1) ({{ (prob (x = k)) = (prob true) }}). 

Theorem ifthen_01 : forall (k : nat), hoare_triple (fun ps : Pstate => ((1/(INR k + 1)) = fst ps (fun st : state => True))%R /\ (snd ps y1) = (1/(INR k + 1))%R) (<{ x := 0 }>) 
                                                    (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = 0%nat))%R).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x 0 (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = 0%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> 0; (fst st)) x) = 0)) with (fst ps {{true}}).
          transitivity ((1 / ((INR k) + 1))%R). easy. easy. apply equivalence. intro. rewrite t_update_eq. easy.
        + apply HTAsgn.
Qed.

Theorem ifthen_02 : forall (k : nat), hoare_triple (fun ps : Pstate => (1 - (1/(INR k + 1)) = fst ps (fun st : state => True))%R /\ (snd ps y2) = 0%R) (<{ x := x + 1 }>) 
                                                    (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = 0%nat))%R).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x <{ x + 1 }> (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = 0%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> ((fst st x) + 1)%nat; (fst st)) x) = 0)) with (fst ps {{false}}).
          transitivity 0%R. easy. rewrite empty_set_measure. easy. apply equivalence. intro. rewrite t_update_eq. lia.
        + apply HTAsgn.
Qed.

Theorem ifthen_0_int : forall (k : nat), hoare_triple ((fun ps : Pstate => ((((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => ((fst st) val) <> 0%nat))%R)) /\ (snd ps y1) = (1/(INR k + 1))%R) /\ (snd ps y2) = 0%R ))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
              {{ y1 + y2 = (prob (x = 0)) }}.
Proof. intro. apply HConseqLeft with (eta2 := (psfBpsf (fun ps : Pstate => ((1/(INR k + 1)) = fst ps (fun st : state => True))%R /\ (snd ps y1) = (1/(INR k + 1))%R) (fun ps : Pstate => (1 - (1/(INR k + 1)) = fst ps (fun st : state => True))%R /\ (snd ps y2) = 0%R) (<{ val = 0 }>) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. replace (fst ps (fun st : state => True /\ (0 = (fst st val)))) with (fst ps (fun st : state => (fst st val) = 0)).
        replace (fst ps (fun st : state => True /\ (0 <> (fst st val)))) with (fst ps (fun st : state => (fst st val) <> 0)).  easy.
        apply equivalence. easy. apply equivalence. easy.
      * apply HIfThen. 
        + uncoerce_basic. replace (fun st : state => 0 = (fst st x)) with (fun st : state => (fst st x) = 0). apply ifthen_01.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + uncoerce_basic. replace (fun st : state => 0 = (fst st x)) with (fun st : state => (fst st x) = 0). apply ifthen_02.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
Qed.


Theorem ifthen_0 : forall (k : nat), hoare_triple (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => ((fst st) val) <> 0%nat))%R)))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
          (fun ps : Pstate => ((1/(INR k + 1))%R = fst ps (fun st : state => ((fst st) x) = 0%nat))%R).
Proof. intro. apply HConseq with (eta2 := eta_update_y_p (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => ((fst st) val) <> 0%nat))%R))) y1 (1/(INR k + 1))%R)
                          (eta3 := eta_update_y_p (fun ps : Pstate => (snd ps y1 + 0 = fst ps (fun st : state => ((fst st) x) = 0%nat))%R) y1 (1/(INR k + 1))%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite Rplus_0_r. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p (fun ps : Pstate => ((((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => ((fst st) val) <> 0%nat))%R)) /\ (snd ps y1) = (1/(INR k + 1))%R) ) y2 0%R)
                                                            (eta3 := eta_update_y_p ({{ y1 + y2 = (prob (x = 0)) }}) y2 0%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. replace (fst ps (fun st : state => 0 = (fst st x))) with (fst ps (fun st : state => (fst st x) = 0)).  easy.
            apply equivalence. easy. easy.
          * apply eliminate_y. easy. easy. apply ifthen_0_int.
Qed.

Theorem ifthen_11 : forall (k : nat), hoare_triple (fun ps : Pstate => ((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) x) = k%nat)))%R /\ (snd ps y1) = 0%R) (<{ x := 0 }>) 
                                                    (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x 0 (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> 0; (fst st)) x) = (k+1)%nat)) with (fst ps {{false}}).
          intro. rewrite empty_set_measure. easy. apply equivalence. intro. rewrite t_update_eq. lia. 
        + apply HTAsgn.
Qed.

Theorem ifthen_12 : forall (k : nat), hoare_triple (fun ps : Pstate => (1 - (1/(INR k + 1)) = fst ps (fun st : state => fst st x = k))%R /\ (snd ps y2) = (1 - (1/(INR k + 1)))%R) (<{ x := x + 1 }>) 
                                                    (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R).
Proof. intro. apply HConseqLeft with (eta2 := tasgn_pt x <{ x + 1 }> (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> ((fst st x) + 1)%nat; (fst st)) x) = (k+1)%nat)) with (fst ps (fun st : state => (fst st x) = k)).
          transitivity (1 - (1/(INR k + 1)))%R. easy. easy. apply equivalence. intro. rewrite t_update_eq. lia.
        + apply HTAsgn.
Qed.

Theorem ifthen_1_int : forall (k : nat), hoare_triple ((fun ps : Pstate => ((((1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R)) /\ (snd ps y1) = 0%R) /\ (snd ps y2) = (1 - (1/(INR k + 1)))%R ))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
              {{ y1 + y2 = (prob (x = (k + 1))) }}.
Proof. intro. apply HConseqLeft with (eta2 := (psfBpsf (fun ps : Pstate => ((1/(INR k + 1)) = fst ps (fun st : state => fst st x = k))%R /\ (snd ps y1) = 0%R) (fun ps : Pstate => (1 - (1/(INR k + 1)) = fst ps (fun st : state => fst st x = k))%R /\ (snd ps y2) = (1 - (1/(INR k + 1)))%R) (<{ val = 0 }>) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. replace (fst ps (fun st : state => (((fst st x) = k) /\ ((fst st val) = 0)))) with (fst ps (fun st : state => ((fst st x) = k) /\ (0 = (fst st val)))).
        replace (fst ps (fun st : state => ((fst st x) = k) /\ ((fst st val) <> 0))) with (fst ps (fun st : state => ((fst st x) = k) /\(0 <> (fst st val)) )).  easy.
        apply equivalence. easy. apply equivalence. easy.
      * apply HIfThen. 
        + uncoerce_basic. replace ((fun st : state => ((k + 1)%nat) = (fst st x))) with ((fun st : state => (fst st x) = ((k + 1)%nat))). apply ifthen_11.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + uncoerce_basic. replace (fun st : state => ((k + 1)%nat) = (fst st x)) with (fun st : state => (fst st x) = ((k + 1)%nat)). apply ifthen_12.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
Qed.

Theorem ifthen_1 : forall (k : nat), hoare_triple (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => fst st x = k /\ ((fst st) val) <> 0%nat))%R)))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
          (fun ps : Pstate => ((1 - (1/(INR k + 1)))%R = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R).
Proof. intro. apply HConseq with (eta2 := eta_update_y_p (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => fst st x = k /\ ((fst st) val) <> 0%nat))%R))) y1 0%R)
                          (eta3 := eta_update_y_p (fun ps : Pstate => (snd ps y1 + (1 - (1/(INR k + 1))) = fst ps (fun st : state => ((fst st) x) = (k+1)%nat))%R) y1 0%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite Rplus_0_l. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p (fun ps : Pstate => ((((1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R)) /\ (snd ps y1) = 0%R) ) y2 (1 - (1/(INR k + 1)))%R)
                                                            (eta3 := eta_update_y_p ({{ y1 + y2 = (prob (x = (k + 1))) }}) y2 (1 - (1/(INR k + 1)))%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. replace (fst ps (fun st : state => (k + 1)%nat = (fst st x))) with (fst ps (fun st : state => (fst st x) = (k + 1)%nat)).  easy.
            apply equivalence. easy. easy.
          * apply eliminate_y. easy. easy. apply ifthen_1_int.
Qed.

Theorem ifthen_void1 : forall (k k1: nat), (k1 <> 0) -> (k1 <> (k + 1)%nat) -> hoare_triple ({{((prob (x = k)) = (prob true)) /\ y1 = 0}}) (<{ x := 0 }>) 
                                                    (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R).
Proof. intros. apply HConseqLeft with (eta2 := tasgn_pt x 0 (fun ps : Pstate => (snd ps y1 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> 0; (fst st)) x) = (k1)%nat)) with (fst ps {{false}}).
          intro. rewrite empty_set_measure. easy. apply equivalence. intro. rewrite t_update_eq. lia. 
        + apply HTAsgn.
Qed.

Theorem ifthen_void2 : forall (k k1: nat), (k1 <> 0) -> (k1 <> (k+1)%nat) -> hoare_triple ({{((prob (x = k)) = (prob true)) /\ y2 = 0}}) (<{ x := x + 1 }>) 
                                                    (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R).
Proof. intros. apply HConseqLeft with (eta2 := tasgn_pt x <{ x + 1 }> (fun ps : Pstate => (snd ps y2 = fst ps (fun st : state => ((fst st) x) = (k1)%nat))%R)).
        + intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. replace (fst ps (fun st : state => ((x !-> ((fst st x) + 1)%nat; (fst st)) x) = (k1)%nat)) with (fst ps (fun st : state => ((fst st x) + 1)%nat = k1)).
          transitivity 0%R. easy. destruct H1. apply measure_P_eq_true in H1. apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H1. apply measure_inclusion. intro. uncoerce_basic. lia. easy.
        + apply HTAsgn.
Qed.

Theorem ifthen_void_int : forall (k k1: nat), (k1 <> 0) -> (k1 <> (k+1)%nat) -> hoare_triple ((fun ps : Pstate => (((fst ps (fun st : state => (fst st val = 0)%nat) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((fst ps (fun st : state => (fst st val <> 0)%nat) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R)) /\ (snd ps y1) = 0%R) /\ (snd ps y2) = 0%R ))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
              {{ y1 + y2 = (prob (x = (k1))) }}.
Proof. intros. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (x = k)) = (prob true)) /\ y1 = 0}}) ({{((prob (x = k)) = (prob true)) /\ y2 = 0}}) (<{ val = 0 }>) )). 
      * intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. simpl. uncoerce_basic. replace (fst ps (fun st : state => (((fst st x) = k) /\ ((fst st val) = 0)))) with (fst ps (fun st : state => (k = (fst st x) ) /\ (0 = (fst st val)))).
        replace (fst ps (fun st : state => ((fst st x) = k) /\ ((fst st val) <> 0))) with (fst ps (fun st : state => (k = (fst st x) ) /\(0 <> (fst st val)) )). 
        replace (fst ps (fun st : state => True /\ (0 = (fst st val)))) with (fst ps (fun st : state => (fst st val) = 0)).
        replace (fst ps (fun st : state => True /\ (0 <> (fst st val)))) with (fst ps (fun st : state => (fst st val) <> 0)). easy.
        apply equivalence. easy. apply equivalence. easy. apply equivalence. easy. apply equivalence. easy.
      * apply HIfThen. 
        + uncoerce_basic. replace ((fun st : state => ((k1)%nat) = (fst st x))) with ((fun st : state => (fst st x) = ((k1)%nat))). apply ifthen_void1. easy. easy.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + uncoerce_basic. replace (fun st : state => ((k1)%nat) = (fst st x)) with (fun st : state => (fst st x) = ((k1)%nat)). apply ifthen_void2. easy. easy.
          apply functional_extensionality. intro. apply propositional_extensionality. easy.
Qed.

Theorem ifthen_void : forall (k k1: nat), (k1 <> 0) -> (k1 <> (k+1)%nat) -> hoare_triple ((fun ps : Pstate => ((fst ps (fun st : state => (fst st val = 0)%nat) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((fst ps (fun st : state => (fst st val <> 0)%nat) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R))))
              (<{if val = 0 then x := 0 else x := x + 1 end}>)
          {{0 = (prob (x = k1)) }}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ((fun ps : Pstate => ((fst ps (fun st : state => (fst st val = 0)%nat) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((fst ps (fun st : state => (fst st val <> 0)%nat) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R)))) y1 0%R)
                          (eta3 := eta_update_y_p ({{0 + y1 = (prob (x = k1)) }}) y1 0%R).
        + easy.
        + intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite Rplus_0_l. simpl.  easy.
        + apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ((fun ps : Pstate => ((fst ps (fun st : state => (fst st val = 0)%nat) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((fst ps (fun st : state => (fst st val <> 0)%nat) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R))/\ snd ps y1 = 0%R)) y2 0%R)
                                                            (eta3 := eta_update_y_p ({{ y1 + y2 = (prob (x = (k1))) }}) y2 0%R).
          * easy.
          * intro. unfold eta_update_y_p. unfold pstate_update. simpl. rewrite t_update_eq. rewrite t_update_neq. uncoerce_basic. lra. 
             easy.
          * apply eliminate_y. easy. easy. apply ifthen_void_int. easy. easy.
Qed.

Theorem bodyvoid : forall (k k1: nat), (k1 <> 0) -> (k1 <> (k+1)%nat) -> hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>))
                    {{0 = (prob (x = k1)) }}.
Proof. intros. apply HSeq with (eta2 := {{(prob (x = k)) = (prob true)}}).
        + apply x_inv.
        + apply HConseqLeft with (eta2 := ((fun ps : Pstate => ((fst ps (fun st : state => (fst st val = 0)%nat) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((fst ps (fun st : state => (fst st val <> 0)%nat) = fst ps (fun st : state => (fst st x = k)%nat /\ ((fst st) val) <> 0%nat))%R))))).
          * uncoerce_basic. intro. intro. rewrite measure_true_dest with (Q := (fun st : state => (fst st x) = k)) in H1.
            symmetry in H1. replace (fst ps (fun st : state => k = (fst st x))) with (fst ps (fun st : state => (fst st x) = k)) in H1. apply Rplus_0_r_uniq in H1. split.
            - symmetry.
              transitivity (fst ps (fun st : state =>  ((fst st val) = 0) /\ ~ ((fst st x) <> k))). apply equivalence. intro. lia.  
              rewrite measure_AnotB. replace (fst ps (fun st : state => ((fst st val) = (0%nat)) /\ ((fst st x) <> k))) with 0%R. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H1. apply measure_inclusion. easy.
            - symmetry.
              transitivity (fst ps (fun st : state =>  ((fst st val) <> 0) /\ ~ ((fst st x) <> k))). apply equivalence. intro. lia.  
              rewrite measure_AnotB. replace (fst ps (fun st : state => ((fst st val) <> (0%nat)) /\ ((fst st x) <> k))) with 0%R. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H1. apply measure_inclusion. easy.
            - apply equivalence. easy.
          * apply ifthen_void. easy. easy.
Qed.

Theorem body0 : forall (k : nat), 
  hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>))
                (fun ps : Pstate => ((1/(INR k + 1))%R = fst ps (fun st : state => ((fst st) x) = 0%nat))%R).
Proof. intros. apply HSeq with (eta2 := (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => ((fst st x = k) /\ ((fst st) val) = 0%nat)))%R) /\ ( ((1-(1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ ((fst st) val) <> 0%nat))%R) )
                                                                /\ (fst ps (fun st : state => (fst st x = k)) = fst ps (fun st : state => True)))).
        + apply HAnd. apply uniform. apply HAnd. apply uniform_neg. apply HConseqRight with (eta2 := ({{ (prob (x = k)) = (prob true) }})). intro. uncoerce_basic.
          intro. transitivity (fst ps (fun st : state => k = (fst st x))). apply equivalence. easy. easy. apply x_inv.
        + apply HConseqLeft with (eta2 := (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => ((fst st) val) <> 0%nat))%R)))).
          * intro. intro. rewrite measure_true_dest with (Q := (fun st : state => (fst st x) = k)) in H.
            destruct H. destruct H0. symmetry in H1. apply Rplus_0_r_uniq in H1. split. 
            - transitivity  (fst ps (fun st : state => ((fst st x) = k) /\ ((fst st val) = 0))). easy.
              transitivity (fst ps (fun st : state =>  ((fst st val) = 0) /\ ~ ((fst st x) <> k))). apply equivalence. intro. lia.  
              rewrite measure_AnotB. replace (fst ps (fun st : state => ((fst st val) = (0%nat)) /\ ((fst st x) <> k))) with 0%R. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H1. apply measure_inclusion. easy.
            - transitivity  (fst ps (fun st : state => ((fst st x) = k) /\ ((fst st val) <> 0))). easy.
              transitivity (fst ps (fun st : state =>  ((fst st val) <> 0) /\ ~ ((fst st x) <> k))). apply equivalence. intro. lia.  
              rewrite measure_AnotB. replace (fst ps (fun st : state => ((fst st val) <> (0%nat)) /\ ((fst st x) <> k))) with 0%R. lra.
              apply Rle_antisym. apply Rge_le. apply positive. rewrite <- H1. apply measure_inclusion. easy.
          * apply ifthen_0.
Qed.

Theorem body1 : forall (k : nat), 
  hoare_triple ({{(prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}) (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>))
    (fun ps : Pstate => ((1 - (1/(INR k + 1)))%R = fst ps (fun st : state => ((fst st) x) = (k + 1)%nat))%R).
Proof. intros. apply HSeq with (eta2 := (fun ps : Pstate => (((1/(INR k + 1)) = fst ps (fun st : state => (fst st x = k) /\ (((fst st) val) = 0%nat)))%R /\ ((1-(1/(INR k + 1)) = fst ps (fun st : state => fst st x = k /\ ((fst st) val) <> 0%nat))%R)))).
        apply HAnd. apply uniform. apply uniform_neg. apply ifthen_1.
Qed.
 

Definition Escaping_spline : Cmd :=
CSeq (<{x := 1}>) (While <{1 <= x}> (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>)) ).

Definition Espline_loop : Cmd := While <{1 <= x}> (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>)).

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
      | S m => (((1 / (INR n + 1))%R) :: T_vector m)%vector
end.

Fixpoint T_list (n : nat) : list R := 
  match n with
      | O => []%list  
      | S m => (((1 / (INR n + 1))%R) :: T_list m)%list
end.

Fixpoint P_vector_int (m i : nat) : Vector.t R m :=
  match m with 
    | O => []%vector
    | S k => if (m =? i) then ((1-(1/INR i))%R :: P_vector_int k i)%vector
                        else (0%R :: P_vector_int k i)%vector
end.


Fixpoint P_vector (n m : nat) : (Vector.t (Vector.t R m) n) :=
    match n with
     | O => []%vector
     | S k => ((P_vector_int m (n+1)) :: P_vector k m)%vector
end.

Fixpoint X_vector_int (n i : nat) : Vector.t R i :=
    match i with 
      | O => []%vector
      | S k => ((1 - ( INR i/ (INR n + 1)))%R :: (X_vector_int n k))%vector
end.

Definition X_vector (n : nat) : Vector.t R n := X_vector_int n n.

Compute P_vector 2 2.
Compute P_vector 3 3.

Compute X_vector 3.

Fixpoint vappend {T : Type} {n m} (v1 : t T n) (v2 : t T m)
  : t T (plus n m) :=
  match v1 in t _ n return t T (plus n m) with
  | []%vector => v2
  | (x :: v1')%vector => (x :: vappend v1' v2)%vector
  end.

Fixpoint plus_n_S n m : ((n + S m) = S (n + m))%nat :=
  match n with
  | 0 => eq_refl
  | S n => f_equal S (plus_n_S n m)
  end.

Fixpoint plus_n_O n : ((n + 0) = n)%nat :=
  match n with
  | 0 => eq_refl
  | S n => f_equal S (plus_n_O n)
  end.

Fixpoint vreverse {T : Type} {n} (v : t T n) : t T n :=
  match v in t _ n return t T n with
  | []%vector => []%vector
  | (x :: v)%vector =>
    eq_rect _ (t T)
      (eq_rect _ (t T) (vappend (vreverse v) [x]%vector) _ (plus_n_S _ 0))
              _ (f_equal S ( plus_n_O _))
  end.

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

Lemma helperXvec : forall (n i : nat), (to_list (X_vector_int n (S i))) = (1 - ( INR (S i)/ (INR n + 1)))%R :: to_list (X_vector_int n i).
Proof. intro. unfold X_vector_int. unfold to_list. easy.
Qed.

Lemma helperXvec1_int : forall (n m i : nat), (i < m) -> nth i (to_list (X_vector_int n m)) 0%R = (1 - ( INR (m - i)/ (INR n + 1)))%R.
Proof. induction m. 
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec i 0).
          * rewrite e. reflexivity.
          * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. simpl. rewrite IHm. reflexivity. lia.
Qed.

Lemma helperXvec1 : forall (n i : nat), (i < n) -> nth i (to_list (X_vector n)) 0%R =   (1 - ( INR (n - i)/ (INR n + 1)))%R.
Proof. intros. unfold X_vector. rewrite helperXvec1_int. reflexivity. easy.
Qed.  

Lemma helperXvect1 : forall (n i m: nat), (i < n) -> (nth i (to_list (P_vector n m)) (const 0%R m)) = P_vector_int m (S (n - i)).
Proof. induction n. intros.
        + assert (~ (i < 0)). lia. contradiction.
        + intros. destruct (Nat.eq_dec i 0).
          * simpl. rewrite e. replace (S (n + 1)) with (S (S n)).  reflexivity. lia.
          * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. simpl. unfold to_list in IHn.
                 rewrite IHn. reflexivity. rewrite H1 in H. lia.
Qed. 

Lemma helperVecSum : forall (m n i : nat), i > 0 -> (vector_sum (zip Rmult  (P_vector_int m i) (X_vector_int n m))) = if (m <? i) then (0%R) else ((1 - (1/ INR i))*(1 - (INR i)/(INR n + 1)))%R.
Proof. intros m n i H. induction m.
        + simpl. replace (0 <? i) with (Datatypes.true). easy. symmetry. apply ltb_lt. easy.
        + unfold P_vector_int. destruct (Nat.eq_dec (S m) i).
          * replace ((S m) =? i) with Datatypes.true. simpl. destruct (Nat.eq_dec m 0).
            ** unfold X_vector_int. rewrite e0. simpl. replace (1 <? i) with (Datatypes.false). rewrite Rplus_0_r. 
               replace (INR i) with 1%R. lra. replace i with 1. simpl. reflexivity.
                lia. replace i with 1. easy. lia.
            ** assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, m = (S k1)). apply T. apply n0. inversion H0. rewrite H1.
                unfold P_vector_int in IHm. unfold X_vector in IHm. unfold X_vector_int in IHm. rewrite H1 in IHm. unfold X_vector_int.
                rewrite IHm. rewrite <- H1. rewrite e. replace (m <? i) with (Datatypes.true).
                replace (i <? i) with (Datatypes.false). rewrite <- e. rewrite Rplus_0_r. Search INR. replace (S m) with (m + 1)%nat. rewrite plus_INR.
                rewrite INR_1. easy. lia. Search "ltb" in Nat. symmetry. apply ltb_irrefl. symmetry. apply ltb_lt. lia.
            ** symmetry. apply Nat.eqb_eq. easy.
         * replace ((S m) =? i) with Datatypes.false. simpl. destruct (Nat.eq_dec m 0).
            ** unfold X_vector_int. rewrite e. simpl. replace (1 <? i) with (Datatypes.true). rewrite Rplus_0_r. rewrite Rmult_0_l. easy. symmetry. 
                apply ltb_lt. lia. 
            **  rewrite Rmult_0_l. unfold P_vector_int in IHm. rewrite IHm.
            rewrite Rplus_0_l. destruct (lt_dec m i). replace (m <? i) with (Datatypes.true). replace (S m <? i) with (Datatypes.true).
            easy. symmetry. apply ltb_lt. lia. symmetry. apply ltb_lt. lia.
            replace (m <? i) with (Datatypes.false). replace (S m <? i) with (Datatypes.false).
            easy. symmetry. apply ltb_nlt. lia. symmetry. apply ltb_nlt. lia.
            ** symmetry. apply Nat.eqb_neq. lia.
Qed. 

Lemma helperVecSum_int1 : forall (n i : nat), (i > 0) -> (i <= n) -> (vector_sum (zip Rmult  (P_vector_int n (S i)) (X_vector n))) = ((1 - (1/ INR (S i)))*(1 - (INR (S i))/(INR n + 1)))%R.
Proof. intros. unfold X_vector. rewrite helperVecSum. destruct (Nat.eq_dec n i).
        + rewrite e. replace (i <? (S i)) with (Datatypes.true). Search INR. rewrite S_INR. field. rewrite <- S_INR. Search INR. rewrite <- INR_0. apply not_INR. lia.
          symmetry. rewrite ltb_lt. lia. 
        + replace ( n <? S i ) with (Datatypes.false). easy. symmetry. rewrite ltb_nlt. lia.
        + lia.
Qed. 



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

Lemma helperTvec : forall (n i : nat), (i < n) -> (List.nth i (to_list (T_vector n)) (0%R)) = (1/(INR (n - i) + 1))%R.
Proof. induction n.
        + intros. assert (~ (i < 0)). lia. contradiction.
        + intro i. destruct (Nat.eq_dec i 0).
          * rewrite e. intro. reflexivity. 
          * intro. unfold to_list. simpl. 
            assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, i = (S k1)). apply T. apply n0. inversion H0. rewrite H1. apply IHn. lia.
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

Lemma helper3 : forall (i n : nat), (i < n) ->  ((List.nth i (to_list (T_vector n)) (0%R)) > 0)%R.
Proof. intros. rewrite helperTvec. rewrite Rdiv_1_l. Search "lt_gt". apply Rlt_gt. apply Rinv_0_lt_compat. apply Rplus_lt_0_compat.
       Search INR. rewrite <- INR_0. Search INR. apply lt_INR. lia. lra. easy.
Qed. 

Lemma helper4 : forall (n m: nat), (n > 0) -> hoare_triple (int_true_eq_one (CBoolexp_of_bexp (<{x = n}>)))
      (CSeq (uniform_xplus1) <{if val = 0 then x := 0 else x := (x + 1) end}>)
      (inner_conj_geq (G_vector m) (P_vector_int m (S n))).
Proof. intro. induction m. 
        + intro. simpl. unfold inner_conj_geq. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip.
          unfold PAssertion_conj. unfold int_true_eq_one. uncoerce_basic. apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3 := (fun ps : Pstate => ((1/(INR n + 1))%R = fst ps (fun st : state => ((fst st) x) = 0%nat))%R)).
          * intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (fst st x) = n)) with (fst ps (fun st : state => n = (fst st x))).
           easy. apply equivalence. easy.
          * easy.
          * apply body0. 
        + intro. simpl. destruct (Nat.eq_dec m n).
          * replace (m =? n) with (Datatypes.true). unfold inner_conj_geq. unfold PAssertion_conj. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip. simpl. intros. apply HAnd.
            -- rewrite e. assert (T: forall (k : nat), k > 0 -> exists k1, k = (S k1)). 
                - intro. destruct k. lia. intro. exists k. reflexivity.
                - assert (exists k1 : nat, n = (S k1)). apply T. apply H. inversion H0. rewrite H1. unfold gamma_geq. unfold gamma_compare. 
                  apply HConseq with (eta2 := ({{(prob ((x0 + 1) = x)) = 1 /\ (prob ((x0 + 1) = x)) = (prob true) }})) (eta3  := fun ps : Pstate => ((1 - (1/(INR (x0 + 1) + 1)))%R = fst ps (fun st : state => ((fst st) x) = ((x0 + 1) + 1)%nat))%R).
                  ** intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (S x0) = (fst st x))) with (fst ps (fun st : state => (fst st x) = ((x0 + 1)%nat))). easy.
                     apply equivalence. intro. lia.
                  ** intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. destruct (Nat.eq_dec x0 0).
                      rewrite e0. intro. apply Req_ge. symmetry. transitivity (fst ps (fun st : state => (fst st x) = (((0 + 1) + 1)%nat))).
                      rewrite add_0_l in H2. rewrite INR_1 in H2. apply H2. apply equivalence. intro. lia.
                      assert (exists x1 : nat, x0 = (S x1)). apply T. lia. inversion H2.  rewrite H3. intro.
                      apply Req_ge. symmetry. transitivity (fst ps (fun st : state => (fst st x) = ((((S x1) + 1) + 1)%nat))). Search INR. rewrite <- S_INR. replace (S (S x1)) with ((S x1) + 1)%nat. apply H4. lia.
                      apply equivalence. intro. lia.
                  ** uncoerce_basic. apply body1.  
            -- apply IHm. easy. 
            -- symmetry. apply Nat.eqb_eq. easy.
          * replace (m =? n) with (Datatypes.false). unfold inner_conj_geq. unfold PAssertion_conj. unfold zip_gamma_geq. unfold zip_gamma_compare. unfold zip. simpl. apply HAnd.
            -- apply HConseq with (eta2 := ({{(prob (n = x)) = 1 /\ (prob (n = x)) = (prob true) }})) (eta3 := {{0 = (prob (x = (m + 1))) }}).
                ** intro. unfold int_true_eq_one. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. replace (fst ps (fun st : state => (fst st x) = n)) with(fst ps (fun st : state => n = (fst st x))).
                   easy. apply equivalence. intro. lia.
                **  intro. unfold gamma_geq. unfold gamma_compare. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. intro. apply Req_ge. symmetry. transitivity (fst ps (fun st : state => ((m + 1)%nat) = (fst st x))).
                    easy. apply equivalence. intro. lia.
                **  uncoerce_basic. apply bodyvoid with (k := n) (k1 := ( m + 1)%nat). lia. lia. 
            -- apply IHm. easy.
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

Lemma helper6_int : forall (n i : nat), (i > 0) -> (nth (i - 1) (Vector.to_list (X_vector_int n i)) 0%R) = (1 - 1 / (INR n + 1))%R.
Proof. intro. induction i.
        + assert (~ (0 < 0)). lia. contradiction.
        + intro. rewrite helperXvec. unfold nth. destruct (Nat.eq_dec ((S i) - 1) 0).
            * replace ((S i)-1) with 0. assert (S i = 1). lia. rewrite H0. easy.  
            * assert (T: forall (k : nat), k <>0 -> exists k1, k = (S k1)).
              - intro. destruct k. contradiction. intro. exists k. reflexivity.
              - assert (exists k1 : nat, (S i) - 1 = (S k1)). apply T. apply n0. inversion H0. rewrite H1.
                unfold nth in IHi. replace x0 with (i - 1). apply IHi. lia. lia.
Qed.

Lemma helper6 : forall (n : nat), (n > 0) -> (nth (n - 1) (Vector.to_list (X_vector n)) 0%R) = (1 - 1 / (INR n + 1))%R.
Proof. unfold X_vector. intro. apply helper6_int with (i := n).
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


Theorem Espline_term_int : forall (n : nat) (b : bexp) (tempA : Assertion), (n >0) -> (b = (Leq (Const 1) (Var x))) -> Assertion_equiv tempA (CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) -> 
        hoare_triple ({{(prob (b /\ tempA)) >= y1 /\ (prob (b /\ tempA)) = (prob true)}}) 
      (While b (CSeq (uniform_xplus1) (<{if val = 0 then x := 0 else x := x + 1 end}>)) )
 (fun ps : Pstate => ((1 - (1/(INR n + 1)))*(snd ps y1) <= fst ps (fun st : state => (fst st x = 0)%nat) )%R).
Proof. intros. eapply HWhileLB2 with (m := n) (G := G_vector n) (T := T_vector n) (P := P_vector n n) (X := X_vector n) (i := n - 1).
        + rewrite H0. apply helper1.
        + intros. apply helper2. easy. easy.
        + intro. intro. left. apply helper3. easy.
        + unfold antgeq2. intros. apply HAnd. apply HConseqLeft with (eta2 := (int_true_eq_one (CBoolexp_of_bexp (Eq (Const (n - i)) (Var x) )))).
          * apply helperGvec_int_true. easy.
          * rewrite helperXvect1 with (n := n) (m := n). apply helper4. lia. lia.
          * rewrite helperTvec. unfold gamma_geq. apply HConseqLeft with (eta2 := (int_true_eq_one (CBoolexp_of_bexp (Eq (Const (n - i)) (Var x) )))).
            - apply helperGvec_int_true. easy.
            - unfold gamma_compare. uncoerce_basic. apply HConseq with (eta2 := ((fun st : Pstate =>
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
       PAssertion) st)))) (eta3 := (fun ps : Pstate => ((1/((INR (n - i)) + 1))%R = fst ps (fun st : state => ((fst st) x) = 0%nat))%R)). 
              -- intro. unfold int_true_eq_one.  uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. 
                  replace (fst ps (fun st2 : state => (fst st2 x) = (n - i))) with (fst ps (fun st : state => (n - i) = (fst st x))). easy. apply equivalence. intro. lia. 
              -- intro. intro. replace (fst ps (fun st : state => (~ (CBoolexp_of_bexp b0 st)) /\ ((fst st x) = (0%nat)))) with (fst ps (fun st : state => (fst st x) = 0)).
                 rewrite <- H3. lra. apply equivalence. intro. unfold CBoolexp_of_bexp. rewrite H0. unfold Beval. unfold Teval. lia.
              -- apply body0 with (k := n - i). 
            - easy. 
        + intros. unfold lin_ineq_lb. simpl. rewrite helperXvect1. rewrite helperVecSum_int1. rewrite helperTvec. rewrite helperXvec1. apply Req_le. 
          admit. 
          easy. easy. lia. lia. easy.
        + lia. 
        + intros. Search "iff" in Logic. apply iff_trans with ( B:= ((CBoolexp_of_bexp ((Eq (Const 1) (Var x)))) st)). apply helper5. easy. easy.
        + rewrite helper6. rewrite Rdiv_def. lra. easy.
Admitted.

Theorem Espline_term_y : forall (n : nat), (n > 0) -> hoare_triple ({{(prob (x = 1)) >= y1 /\ (prob (x = 1)) = (prob true)}}) 
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
Qed.


      
