From PHL Require Import Maps.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import EqNat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Reals.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Init.Logic.
From Coq Require Import Lra.
From Coq Require Import String.
Import Vector.VectorNotations.
From Coq Require Import Vector.
Require Import Classical.
From PHL Require Import PHLTest.
Import PHL.

Module CondSamples.

(* A formal proof that x and y are independent conditioned on z at the end of the program CondSamples
  take from LILAC (Li, Ahmed, Holtzen) PLDI 2023. *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition y1 : string := "y1".
Definition y2 : string := "y2".

Definition CondSamples (p : R) (q : R) : Cmd :=
<{
  z toss 0.5;
  if z then x toss p; y toss p
      else x toss q; y toss q end
  
}>.

Lemma z_true_1 : forall (p : R), hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = 0.5 }}) <{ x toss p; y toss p }> ({{(prob (z <-> true)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := ({{(prob (z <-> true)) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob (z <-> true)) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((x !-> True; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). 
            replace (fst ps (fun st : state => ((x !-> False; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob (z <-> true)) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((y !-> True; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). 
            replace (fst ps (fun st : state => ((y !-> False; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) <{ x toss q; y toss q }> ({{(prob (z <-> true)) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := ({{(prob (z <-> true)) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob (z <-> true)) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((x !-> True; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). 
            replace (fst ps (fun st : state => ((x !-> False; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob (z <-> true)) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((y !-> True; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). 
            replace (fst ps (fun st : state => ((y !-> False; (snd st)) z) <-> True)) with (fst ps (fun st : state => ((snd st) z) <-> True)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma z_true_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = 0.5) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (z <-> true)) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = 0.5 }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => (snd st z) <-> True))) with (fun ps : Pstate => (fst ps (fun st : state => (snd st z) <-> True)) = (snd ps y1)).
            apply z_true_1 with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => (snd st z) <-> True))) with (fun ps : Pstate => (fst ps (fun st : state => (snd st z) <-> True)) = (snd ps y2)).
            apply z_true_2 with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma z_true : forall (p q : R), hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5 = (prob (z <-> true)) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 0.5%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob (z <-> true)) }}) y1 0.5%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = 0.5 }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (z <-> true)) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply z_true_int.
Qed.

Lemma z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob (z <-> false)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := ({{(prob (z <-> false)) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob (z <-> false)) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((x !-> True; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps (fun st : state => ((x !-> False; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob (z <-> false)) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((y !-> True; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps (fun st : state => ((y !-> False; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma z_false_2 : forall (q : R), hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = 0.5 }}) <{ x toss q; y toss q }> ({{(prob (z <-> false)) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := ({{(prob (z <-> false)) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob (z <-> false)) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((x !-> True; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps (fun st : state => ((x !-> False; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob (z <-> false)) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps (fun st : state => ((y !-> True; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps (fun st : state => ((y !-> False; (snd st)) z) <-> False)) with (fst ps (fun st : state => ((snd st) z) <-> False)). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma z_false_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = 0.5}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (z <-> false)) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = 0.5 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => (snd st z) <-> False))) with (fun ps : Pstate => (fst ps (fun st : state => (snd st z) <-> False)) = (snd ps y1)).
            apply z_false_1 with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => (snd st z) <-> False))) with (fun ps : Pstate => (fst ps (fun st : state => (snd st z) <-> False)) = (snd ps y2)).
            apply z_false_2 with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma z_false : forall (p q : R), hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5 = (prob (z <-> false)) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + 0.5 = (prob (z <-> false)) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 0.5%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (z <-> false)) }}) y2 0.5%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply z_false_int.
Qed.

Lemma x_true_z_true_1 : forall (p : R), hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p) }}) <{ x toss p; y toss p }> ({{(prob ((x <-> true) /\ (z <-> true))) = y1 }}). 
Proof. intro p. apply HSeq with (eta2 := ({{(prob ((x <-> true) /\ (z <-> true))) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob ((x <-> true) /\ (z <-> true))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> True) /\ (((x !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> True) /\ (((x !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob ((x <-> true) /\ (z <-> true))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> True) /\ (((y !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> True) /\ (((y !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> True))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_true_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> true) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := ({{(prob ((x <-> true) /\ (z <-> true))) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob ((x <-> true) /\ (z <-> true))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> True) /\ (((x !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> True) /\ (((x !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob ((x <-> true) /\ (z <-> true))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> True) /\ (((y !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> True) /\ (((y !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> True))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_true_z_true_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> True))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> True))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_z_true : forall (p q : R), hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*p) = (prob ((x <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*p)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> true) /\ (z <-> true))) }}) y1 (0.5*p)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> true) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_z_true_int.
Qed.

Lemma x_false_z_true_1 : forall (p t : R), t = (1 - p)%R ->
  hoare_triple
    ({{ ((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t) }})
    <{ x toss p; y toss p }>
    ({{ (prob ((x <-> false) /\ (z <-> true))) = y1 }}).
Proof.
  intros p t Ht.
  apply HSeq with (eta2 := ({{(prob ((x <-> false) /\ (z <-> true))) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob ((x <-> false) /\ (z <-> true))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> False) /\ (((x !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
         False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> False) /\ (((x !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
          (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob ((x <-> false) /\ (z <-> true))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> False) /\ (((y !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> False) /\ (((y !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> True))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_false_z_true_2 : forall (q : R),
  hoare_triple
    ({{ ((prob (z <-> true)) = 0) /\ y2 = 0 }})
    <{ x toss q; y toss q }>
    ({{ (prob ((x <-> false) /\ (z <-> true))) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := ({{(prob ((x <-> false) /\ (z <-> true))) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob ((x <-> false) /\ (z <-> true))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> False) /\ (((x !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
         False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> False) /\ (((x !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob ((x <-> false) /\ (z <-> true))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> False) /\ (((y !-> True; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> True))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> False) /\ (((y !-> False; (snd st)) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> True))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_false_z_true_int : forall (p q t : R), (t = (1 - p)%R) -> hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> True))) = (snd ps y1)).
            apply H with (p := p). easy. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> True))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_z_true : forall (p q t: R), (t = (1 - p)%R) -> hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t) = (prob ((x <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*t)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> false) /\ (z <-> true))) }}) y1 (0.5*t)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> false) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_z_true_int. easy.
Qed.

Lemma y_true_z_true_1 : forall (p : R), hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p) }}) <{ x toss p; y toss p }> ({{(prob ((y <-> true) /\ (z <-> true))) = y1 }}). 
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((y <-> true) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((y <-> true) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> True))) with (fst ps
         (fun st : state =>
          False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> True))) with (fst ps
         (fun st : state =>
          False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed. 

Lemma y_true_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((y <-> true) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((y <-> true) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((y <-> true) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed. 

Lemma y_true_z_true_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((y <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose y_true_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> True))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose y_true_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> True))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma y_true_z_true : forall (p q : R), hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*p) = (prob ((y <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*p)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((y <-> true) /\ (z <-> true))) }}) y1 (0.5*p)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((y <-> true) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply y_true_z_true_int.
Qed.

Lemma y_false_z_true_1 : forall (p t : R), t = (1 - p)%R ->
  hoare_triple
    ({{ ((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t) }})
    <{ x toss p; y toss p }>
    ({{ (prob ((y <-> false) /\ (z <-> true))) = y1 }}).
Proof.
  intros p t Ht.
  apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((y <-> false) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((y <-> false) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
          (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
          (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed. 

Lemma y_false_z_true_2 : forall (q : R),
  hoare_triple
    ({{ ((prob (z <-> true)) = 0) /\ y2 = 0 }})
    <{ x toss q; y toss q }>
    ({{ (prob ((y <-> false) /\ (z <-> true))) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((y <-> false) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((y <-> false) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
         False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> True))) with (fst ps
       (fun st : state =>
        (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed.

Lemma y_false_z_true_int : forall (p q t : R), (t = (1 - p)%R) -> hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose y_false_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y1) = (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> True))) = (snd ps y1)).
            apply H with (p := p). easy. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose y_false_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate => (snd ps y2) = (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> True)))) with (fun ps : Pstate => (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> True))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma y_false_z_true : forall (p q t: R), (t = (1 - p)%R) -> hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t) = (prob ((y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*t)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((y <-> false) /\ (z <-> true))) }}) y1 (0.5*t)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((y <-> false) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply y_false_z_true_int. easy.
Qed.

Lemma x_true_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob ((x <-> true) /\ (z <-> false))) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := ({{(prob ((x <-> true) /\ (z <-> false))) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob ((x <-> true) /\ (z <-> false))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> True) /\ (((x !-> True; (snd st)) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> True) /\ (((x !-> False; (snd st)) z) <-> False))) with (fst ps (fun st : state => False)).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob ((x <-> true) /\ (z <-> false))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> True) /\ (((y !-> True; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> False))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> True) /\ (((y !-> False; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> False))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_true_z_false_2 : forall (q : R), hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> true) /\ (z <-> false))) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := ({{(prob ((x <-> true) /\ (z <-> false))) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob ((x <-> true) /\ (z <-> false))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> True) /\ (((x !-> True; (snd st)) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> True) /\ (((x !-> False; (snd st)) z) <-> False))) with (fst ps (fun st : state => False)).
            intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. rewrite empty_set_measure. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob ((x <-> true) /\ (z <-> false))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> True) /\ (((y !-> True; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> False))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> True) /\ (((y !-> False; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> True) /\ (((snd st) z) <-> False))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_true_z_false_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*q)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> true) /\ (z <-> false))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) = (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> False))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) = (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st x) <-> True) /\ ((snd st z) <-> False))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_z_false : forall (p q : R), hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5*q = (prob ((x <-> true) /\ (z <-> false))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*q) = (prob ((x <-> true) /\ (z <-> false))) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*q)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> true) /\ (z <-> false))) }}) y2 (0.5*q)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_z_false_int.
Qed.

Lemma x_false_z_false_1 : forall (p : R),hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob ((x <-> false) /\ (z <-> false))) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := ({{(prob ((x <-> false) /\ (z <-> false))) = y1 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x p ({{(prob ((x <-> false) /\ (z <-> false))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> False) /\ (((x !-> True; (snd st)) z) <-> False))) with (fst ps (fun st : state => False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> False) /\ (((x !-> False; (snd st)) z) <-> False))) with (fst ps (fun st : state => (((snd st) z) <-> False))).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y p ({{(prob ((x <-> false) /\ (z <-> false))) = y1 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> False) /\ (((y !-> True; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> False))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> False) /\ (((y !-> False; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> False))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_false_z_false_2 : forall (q t: R), (t = (1 - q)%R) -> hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> false) /\ (z <-> false))) = y2 }}).
Proof. intros q t Ht. apply HSeq with (eta2 := ({{(prob ((x <-> false) /\ (z <-> false))) = y2 }})).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ({{(prob ((x <-> false) /\ (z <-> false))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((x !-> True; (snd st)) x) <-> False) /\ (((x !-> True; (snd st)) z) <-> False))) with (fst ps (fun st : state => False)). 
            replace (fst ps
       (fun st : state =>
        (((x !-> False; (snd st)) x) <-> False) /\ (((x !-> False; (snd st)) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)).
            intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. rewrite empty_set_measure. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HConseqLeft with (eta2 := (btoss_pt y q ({{(prob ((x <-> false) /\ (z <-> false))) = y2 }}))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
       (fun st : state =>
        (((y !-> True; (snd st)) x) <-> False) /\ (((y !-> True; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> False))). 
            replace (fst ps
       (fun st : state =>
        (((y !-> False; (snd st)) x) <-> False) /\ (((y !-> False; (snd st)) z) <-> False))) with (fst ps
       (fun st : state =>
        (((snd st) x) <-> False) /\ (((snd st) z) <-> False))). lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
Qed.

Lemma x_false_z_false_int : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*t)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> false) /\ (z <-> false))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) = (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> False))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) = (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st x) <-> False) /\ ((snd st z) <-> False))) = (snd ps y2)).
            apply H with (q := q). apply Ht. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_z_false : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5*t = (prob ((x <-> false) /\ (z <-> false))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*t) = (prob ((x <-> false) /\ (z <-> false))) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. rewrite Ht. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*t)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> false) /\ (z <-> false))) }}) y2 (0.5*t)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_z_false_int. easy.
Qed.

Lemma y_true_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob ((y <-> true) /\ (z <-> false))) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((y <-> true) /\ (z <-> false))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((y <-> true) /\ (z <-> false))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed.

Lemma y_true_z_false_2 : forall (q : R), hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q) }}) <{ x toss q; y toss q }> ({{(prob ((y <-> true) /\ (z <-> false))) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((y <-> true) /\ (z <-> false))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((y <-> true) /\ (z <-> false))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => ((snd st) z) <-> False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss.
Qed.

Lemma y_true_z_false_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*q)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((y <-> true) /\ (z <-> false))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose y_true_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) = (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> False))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose y_true_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) = (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st y) <-> True) /\ ((snd st z) <-> False))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma y_true_z_false : forall (p q : R), hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5*q = (prob ((y <-> true) /\ (z <-> false))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*q) = (prob ((y <-> true) /\ (z <-> false))) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*q)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((y <-> true) /\ (z <-> false))) }}) y2 (0.5*q)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply y_true_z_false_int.
Qed.

Lemma y_false_z_false_1 : forall (p : R),hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob ((y <-> false) /\ (z <-> false))) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((y <-> false) /\ (z <-> false))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((y <-> false) /\ (z <-> false))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => (((snd st) z) <-> False))).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma y_false_z_false_2 : forall (q t: R), (t = (1 - q)%R) -> hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t) }}) <{ x toss q; y toss q }> ({{(prob ((y <-> false) /\ (z <-> false))) = y2 }}).
Proof. intros q t Ht. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((y <-> false) /\ (z <-> false))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q ( (btoss_pt y q ({{(prob ((y <-> false) /\ (z <-> false))) = y2 }}))))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> True; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> True; (snd st))) z) <-> False))) with (fst ps (fun st : state => (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
          (((y !-> False; (x !-> False; (snd st))) z) <-> False))) with (fst ps (fun st : state => (((snd st) z) <-> False))).
        rewrite empty_set_measure. intro H. destruct H as (H1,H2). rewrite H1. rewrite H2. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma y_false_z_false_int : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*t)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((y <-> false) /\ (z <-> false))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose y_false_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) = (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> False))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose y_false_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) = (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> False)))) with (fun ps : Pstate =>
   (fst ps (fun st : state => ((snd st y) <-> False) /\ ((snd st z) <-> False))) = (snd ps y2)).
            apply H with (q := q). apply Ht. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma y_false_z_false : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{0.5*t = (prob ((y <-> false) /\ (z <-> false))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*t) = (prob ((y <-> false) /\ (z <-> false))) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. rewrite Ht. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*t)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((y <-> false) /\ (z <-> false))) }}) y2 (0.5*t)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply y_false_z_false_int. easy.
Qed.

Lemma x_true_y_true_z_true_1 : forall (p : R), hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p*p) }}) <{ x toss p; y toss p }> ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }}). 
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_true_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_true_z_true_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p*p)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p*p) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_y_true_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True)))) = (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_y_true_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True)))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_y_true_z_true : forall (p q : R), hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*p*p) = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*p*p)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}) y1 (0.5*p*p)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p*p) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_y_true_z_true_int.
Qed.

Lemma x_true_y_false_z_true_1 : forall (p t : R), (t = (1 - p)%R) -> hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p*t) }}) <{ x toss p; y toss p }> ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }}). 
Proof. intros p t Ht. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_false_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_false_z_true_int : forall (p q t : R), (t = (1 - p)%R) -> hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p*t)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*p*t) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_y_false_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True)))) = (snd ps y1)).
            apply H with (p := p). apply Ht. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_y_false_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True)))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_y_false_z_true : forall (p q t: R), (t = (1 - p)%R) -> hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*p*t) = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*p*t)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}) y1 (0.5*p*t)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. rewrite Ht. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*p*t) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_y_false_z_true_int. easy.
Qed.

Lemma x_false_y_false_z_true_1 : forall (p t : R), (t = (1 - p)%R) -> hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t*t) }}) <{ x toss p; y toss p }> ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }}). 
Proof. intros p t Ht. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_false_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_false_z_true_int : forall (p q t : R), (t = (1 - p)%R) -> hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t*t)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t*t) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_y_false_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True)))) = (snd ps y1)).
            apply H with (p := p). apply Ht. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_y_false_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> True)))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_y_false_z_true : forall (p q t: R), (t = (1 - p)%R) -> hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t*t) = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*t*t)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}) y1 (0.5*t*t)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. rewrite Ht. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t*t) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_y_false_z_true_int. easy.
Qed.

Lemma x_false_y_true_z_true_1 : forall (p t : R), (t = (1 - p)%R) -> hoare_triple ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t*p) }}) <{ x toss p; y toss p }> ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }}). 
Proof. intros p t Ht. apply HSeq with (eta2 := (btoss_pt y p ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_true_z_true_2 : forall (q : R), hoare_triple ({{((prob (z <-> true)) = 0) /\ y2 = (0) }}) <{ x toss q; y toss q }> ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }}). 
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> True))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> True)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_true_z_true_int : forall (p q t : R), (t = (1 - p)%R) -> hoare_triple ({{(((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t*p)) /\ y2 = 0}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> true)) = 0.5) /\ y1 = (0.5*t*p) }}) ({{((prob (z <-> true)) = 0) /\ y2 = 0 }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_y_true_z_true_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True)))) = (snd ps y1)).
            apply H with (p := p). apply Ht. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_y_true_z_true_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> True)))) = (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_y_true_z_true : forall (p q t: R), (t = (1 - p)%R) -> hoare_triple ({{(prob (z <-> true)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t*p) = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> True) /\ (snd st z))) with (fst ps (fun st : state => ((snd st z) <-> True))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto.
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) }}) y1 (0.5*t*p)%R) (eta3 := eta_update_y_p ({{y1 + 0 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}) y1 (0.5*t*p)%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. rewrite Ht. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> true) /\ z)) = 0.5) /\ ((prob ((z <-> true)/\ ~ z)) = 0) /\ y1 = (0.5*t*p) }}) y2 0%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}) y2 0%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_y_true_z_true_int. easy.
Qed.

Lemma x_true_y_true_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_true_z_false_2 : forall (q : R), hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q*q) }}) <{ x toss q; y toss q }> ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y2 }}).
Proof. intro q. apply HSeq with (eta2 := (btoss_pt y q ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_true_z_false_int : forall (p q : R), hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*q*q)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (x <-> true) /\ (y <-> true) /\ (z <-> false))  }}).
Proof. intros p q. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q*q) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_y_true_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False)))) =    (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_y_true_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False)))) =    (snd ps y2)).
            apply H with (q := q). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_y_true_z_false : forall (p q : R), hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*q*q) = (prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) }}).
Proof. intros p q. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*q*q) = (prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*q*q)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (x <-> true) /\ (y <-> true) /\ (z <-> false)) }}) y2 (0.5*q*q)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_y_true_z_false_int.
Qed.

Lemma x_true_y_false_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_false_z_false_2 : forall (q t: R), (t = (1 - q)%R) -> hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q*t) }}) <{ x toss q; y toss q }> ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y2 }}).
Proof. intros q t Ht. apply HSeq with (eta2 := (btoss_pt y q ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> True) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_true_y_false_z_false_int : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*q*t)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (x <-> true) /\ (y <-> false) /\ (z <-> false))  }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*q*t) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_true_y_false_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False)))) =    (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_true_y_false_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> True) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False)))) =    (snd ps y2)).
            apply H with (q := q). easy. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_true_y_false_z_false : forall (p q t: R),(t = (1 - q)%R) -> hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*q*t) = (prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*q*t) = (prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*q*t)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (x <-> true) /\ (y <-> false) /\ (z <-> false)) }}) y2 (0.5*q*t)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_true_y_false_z_false_int. easy.
Qed.

Lemma x_false_y_false_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_false_z_false_2 : forall (q t: R), (t = (1 - q)%R) -> hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t*t) }}) <{ x toss q; y toss q }> ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y2 }}).
Proof. intros q t Ht. apply HSeq with (eta2 := (btoss_pt y q ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> False) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_false_z_false_int : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*t*t)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (x <-> false) /\ (y <-> false) /\ (z <-> false))  }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t*t) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_y_false_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False)))) =    (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_y_false_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> False) /\ ((snd st z) <-> False)))) =    (snd ps y2)).
            apply H with (q := q). easy. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_y_false_z_false : forall (p q t: R),(t = (1 - q)%R) -> hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t*t) = (prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*t*t) = (prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*t*t)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (x <-> false) /\ (y <-> false) /\ (z <-> false)) }}) y2 (0.5*t*t)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_y_false_z_false_int. easy.
Qed.

Lemma x_false_y_true_z_false_1 : forall (p : R), hoare_triple ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) <{ x toss p; y toss p }> ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y1 }}).
Proof. intro p. apply HSeq with (eta2 := (btoss_pt y p ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y1 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x p (btoss_pt y p ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y1 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_true_z_false_2 : forall (q t: R), (t = (1 - q)%R) -> hoare_triple ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t*q) }}) <{ x toss q; y toss q }> ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y2 }}).
Proof. intros q t Ht. apply HSeq with (eta2 := (btoss_pt y q ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y2 }}))).
        + apply HConseqLeft with (eta2 := (btoss_pt x q (btoss_pt y q ({{(prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) = y2 }})))).
          - unfold PAImplies. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            intro ps. replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). 
            replace (fst ps
         (fun st : state =>
          (((y !-> True; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> True; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> True; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
         (((snd st) z) <-> False))).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> True; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> True; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> True; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)).
            replace (fst ps
         (fun st : state =>
          (((y !-> False; (x !-> False; (snd st))) x) <-> False) /\
          ((((y !-> False; (x !-> False; (snd st))) y) <-> True) /\
           (((y !-> False; (x !-> False; (snd st))) z) <-> False)))) with (fst ps
       (fun st : state =>
        False)). rewrite empty_set_measure. intro H. destruct H as (H0, H1). rewrite H1. rewrite H0. rewrite Ht. lra.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
          - apply HBToss.
        + apply HBToss. 
Qed.

Lemma x_false_y_true_z_false_int : forall (p q t: R), (t = (1 - q)%R) -> hoare_triple ({{(((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0) /\ y2 = (0.5*t*q)}}) <{if z then x toss p; y toss p
                                                            else x toss q; y toss q end }> ({{y1 + y2 = (prob (x <-> false) /\ (y <-> true) /\ (z <-> false))  }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := (psfBpsf ({{((prob (z <-> false)) = 0) /\ y1 = 0 }}) ({{((prob (z <-> false)) = 0.5) /\ y2 = (0.5*t*q) }}) (z) )).
        + unfold PAImplies. intro ps. easy.
        + apply HIfThen.
          - uncoerce_basic. pose x_false_y_true_z_false_1 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y1) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False)))) =    (snd ps y1)).
            apply H with (p := p). apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
          - uncoerce_basic. pose x_false_y_true_z_false_2 as H. uncoerce_basic_H H. replace (fun ps : Pstate =>
   (snd ps y2) =
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False))))) with (fun ps : Pstate =>
   (fst ps
      (fun st : state => ((snd st x) <-> False) /\ (((snd st y) <-> True) /\ ((snd st z) <-> False)))) =    (snd ps y2)).
            apply H with (q := q). easy. apply functional_extensionality. intro x0. apply propositional_extensionality. lra.
Qed.

Lemma x_false_y_true_z_false : forall (p q t: R),(t = (1 - q)%R) -> hoare_triple ({{(prob (z <-> false)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                      else x toss q; y toss q end }> ({{(0.5*t*q) = (prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) }}).
Proof. intros p q t Ht. apply HConseqLeft with (eta2 := ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }})).
        + unfold PAImplies. intro ps. intro H. split. uncoerce_basic. rewrite <- empty_set_measure with (mu := fst ps). apply equivalence. unfold Assertion_equiv. intro st. tauto. 
          uncoerce_basic. replace (fst ps (fun st : state => ((snd st z) <-> False) /\ (~ (snd st z)))) with (fst ps (fun st : state => ((snd st z) <-> False))).
          apply H. apply equivalence. unfold Assertion_equiv. intro st. tauto.  
        + apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) }}) y1 0%R) (eta3 := eta_update_y_p ({{y1 + (0.5*t*q) = (prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) }}) y1 0%R).
          - easy.
          - unfold PAImplies. unfold eta_update_y_p. intro. uncoerce_basic. rewrite t_update_eq. lra.
          - apply eliminate_y. easy. easy. apply HConseq with (eta2 := eta_update_y_p ({{ ((prob ((z <-> false) /\ z)) = 0) /\ ((prob ((z <-> false)/\ ~ z)) = 0.5) /\ y1 = 0 }}) y2 (0.5*t*q)%R) 
                                                              (eta3 := eta_update_y_p ({{y1 + y2 = (prob (x <-> false) /\ (y <-> true) /\ (z <-> false)) }}) y2 (0.5*t*q)%R).
            * easy.
            * easy.
            * apply eliminate_y. easy. easy. apply x_false_y_true_z_false_int. easy.
Qed.

Definition post_cond (X Y Z : bool) : PAssertion :=
{{(prob (z <-> Z))*(prob((x <-> X) /\ (y <-> Y) /\ (z <-> Z))) = ((prob((x <-> X) /\ (z <-> Z)))*(prob((y <-> Y) /\ (z <-> Z)))) }}.

Theorem if_then_indep: forall (X Y Z : bool) (p q : R), hoare_triple ({{(prob (z <-> Z)) = 0.5 }}) <{if z then x toss p; y toss p
                                                                                        else x toss q; y toss q end }> (post_cond X Y Z).
Proof. intros X Y Z p q. destruct X.
        + destruct Y.
          - destruct Z.
            * unfold post_cond. uncoerce_basic. apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> true)) ) /\ ((0.5*p*p) = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true)))) /\ ((0.5*p) = (prob ((x <-> true) /\ (z <-> true)))) /\ ((0.5*p) = (prob ((y <-> true) /\ (z <-> true))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_true. apply HAnd. apply x_true_y_true_z_true. apply HAnd. apply x_true_z_true. apply y_true_z_true.
            * unfold post_cond. uncoerce_basic. apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> false)) ) /\ ((0.5*q*q) = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false)))) /\ ((0.5*q) = (prob ((x <-> true) /\ (z <-> false)))) /\ ((0.5*q) = (prob ((y <-> true) /\ (z <-> false))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_false. apply HAnd. apply x_true_y_true_z_false. apply HAnd. apply x_true_z_false. apply y_true_z_false.
          - destruct Z.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - p)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> true)) ) /\ ((0.5*p*t) = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true)))) /\ ((0.5*p) = (prob ((x <-> true) /\ (z <-> true)))) /\ ((0.5*t) = (prob ((y <-> false) /\ (z <-> true))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_true. apply HAnd. apply x_true_y_false_z_true. easy. apply HAnd. apply x_true_z_true. apply y_false_z_true. easy.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - q)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> false)) ) /\ ((0.5*q*t) = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false)))) /\ ((0.5*q) = (prob ((x <-> true) /\ (z <-> false)))) /\ ((0.5*t) = (prob ((y <-> false) /\ (z <-> false))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_false. apply HAnd. apply x_true_y_false_z_false. easy. apply HAnd. apply x_true_z_false. apply y_false_z_false. easy.
       + destruct Y.
          - destruct Z.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - p)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> true)) ) /\ ((0.5*t*p) = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true)))) /\ ((0.5*t) = (prob ((x <-> false) /\ (z <-> true)))) /\ ((0.5*p) = (prob ((y <-> true) /\ (z <-> true))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_true. apply HAnd. apply x_false_y_true_z_true. easy. apply HAnd. apply x_false_z_true. easy. apply y_true_z_true.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - q)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> false)) ) /\ ((0.5*t*q) = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false)))) /\ ((0.5*t) = (prob ((x <-> false) /\ (z <-> false)))) /\ ((0.5*q) = (prob ((y <-> true) /\ (z <-> false))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_false. apply HAnd. apply x_false_y_true_z_false. easy. apply HAnd. apply x_false_z_false. easy. apply y_true_z_false.
          - destruct Z.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - p)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> true)) ) /\ ((0.5*t*t) = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true)))) /\ ((0.5*t) = (prob ((x <-> false) /\ (z <-> true)))) /\ ((0.5*t) = (prob ((y <-> false) /\ (z <-> true))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_true. apply HAnd. apply x_false_y_false_z_true. easy. apply HAnd. apply x_false_z_true. easy. apply y_false_z_true. easy.
            * unfold post_cond. uncoerce_basic. pose (t := (1 - q)%R). apply HConseqRight with (eta2:= {{(0.5 = (prob (z <-> false)) ) /\ ((0.5*t*t) = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false)))) /\ ((0.5*t) = (prob ((x <-> false) /\ (z <-> false)))) /\ ((0.5*t) = (prob ((y <-> false) /\ (z <-> false))))}}).
              ** unfold PAImplies. intro ps. uncoerce_basic. intro H. destruct H as (H1,H11). destruct H11 as (H2,H22). destruct H22 as (H3,H4).
                  rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. lra.
              ** apply HAnd. apply z_false. apply HAnd. apply x_false_y_false_z_false. easy. apply HAnd. apply x_false_z_false. easy. apply y_false_z_false. easy.
Qed. 

Lemma toss_stmt : forall (Z : bool), hoare_triple ({{ (prob (true)) = 1  }}) <{ z toss 0.5 }> ({{ (prob (z <-> Z)) = 0.5 }}).
Proof. intro. apply HConseqLeft with (eta2 := (btoss_pt z (0.5%R) ({{ (prob (z <-> Z)) = 0.5 }}))).
        + unfold PAImplies. intro ps. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
          destruct Z.
          - replace (fst ps (fun st : state => ((z !-> True; (snd st)) z) <-> True)) with (fst ps (fun st : state => True)).
            replace (fst ps (fun st : state => ((z !-> False; (snd st)) z) <-> True)) with (fst ps (fun st : state => False)).
            rewrite empty_set_measure. lra. 
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
          - replace (fst ps (fun st : state => ((z !-> True; (snd st)) z) <-> False)) with (fst ps (fun st : state => False)).
            replace (fst ps (fun st : state => ((z !-> False; (snd st)) z) <-> False)) with (fst ps (fun st : state => True)).
            rewrite empty_set_measure. lra. 
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
        + apply HBToss.
Qed.

Theorem cond_indep: forall (X Y Z : bool) (p q : R), hoare_triple ({{ (prob (true)) = 1  }}) (CondSamples p q) (post_cond X Y Z).
Proof. intros X Y Z p q. apply HSeq with (eta2 := ({{ (prob (z <-> Z)) = 0.5 }})). apply toss_stmt. apply if_then_indep. Qed.




End CondSamples.
