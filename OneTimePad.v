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

Module OTP.

(* Formal proof of independence of input m and cypher c after a one time pad. Independence is shown
for a one-bit one time pad and a two-bit version. *)

Definition m : string := "m".
Definition c : string := "c".
Definition b : string := "b".

Definition OneTimePad : Cmd :=
<{ 
  b toss 0.5;
  c b= ((m /\ ~ b) \/ (~ m /\ b))
}>.

Theorem OTP_Input_Indep : forall x y : bool, hoare_triple ({{(prob true) = 1}}) OneTimePad ({{(prob ((c <-> x) /\ (m <-> y))) = ((prob (c <-> x))*(prob (m <-> y)))}}).
Proof. intros x y. apply HSeq with (eta2 := ({{(prob ((((m /\ ~ b) \/ (~ m /\ b)) <-> x) /\ (m <-> y))) = ((prob (((m /\ ~ b) \/ (~ m /\ b)) <-> x))*(prob (m <-> y)))}})).
        + apply HConseqLeft with (eta2 := (btoss_pt (b) (0.5%R) ({{(prob ((((m /\ ~ b) \/ (~ m /\ b)) <-> x) /\ (m <-> y))) = ((prob (((m /\ ~ b) \/ (~ m /\ b)) <-> x))*(prob (m <-> y)))}}))).
          - uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
              replace (fun st : state =>
            (((((b !-> False; (snd st)) m) /\ (~ ((b !-> False; (snd st)) b))) \/
              ((~ ((b !-> False; (snd st)) m)) /\ ((b !-> False; (snd st)) b))) <->
             (if x then True else False)) /\
            (((b !-> False; (snd st)) m) <-> (if y then True else False))) with (fun st : state =>
            (((((snd st) m) /\ (~ False)) \/
              ((~ ((snd st) m) /\ False)) <->
             (if x then True else False)) /\
            (((snd st) m) <-> (if y then True else False)))).
              replace (fun st : state =>
          (((((b !-> True; (snd st)) m) /\ (~ ((b !-> True; (snd st)) b))) \/
            ((~ ((b !-> True; (snd st)) m)) /\ ((b !-> True; (snd st)) b))) <->
           (if x then True else False)) /\
          (((b !-> True; (snd st)) m) <-> (if y then True else False))) with (fun st : state =>
          ((((((snd st) m) /\ (~ True)) \/
            ((~ (snd st) m)) /\ True)) <->
           (if x then True else False)) /\
          (((snd st) m) <-> (if y then True else False))). 
             replace (fun st : state =>
           ((((b !-> True; (snd st)) m) /\ (~ ((b !-> True; (snd st)) b))) \/
            ((~ ((b !-> True; (snd st)) m)) /\ ((b !-> True; (snd st)) b))) <->
           (if x then True else False)) with (fun st : state =>
           ((((snd st) m) /\ (~ True)) \/
            ((~ ((snd st) m)) /\ True)) <->
           (if x then True else False)).
              replace (fun st : state =>
           ((((b !-> False; (snd st)) m) /\ (~ ((b !-> False; (snd st)) b))) \/
            ((~ ((b !-> False; (snd st)) m)) /\ ((b !-> False; (snd st)) b))) <->
           (if x then True else False)) with (fun st : state =>
           ((((snd st) m) /\ (~ False)) \/
            ((~ ((snd st) m)) /\ False)) <->
           (if x then True else False)).
              replace (fun st : state => ((b !-> True; (snd st)) m) <-> (if y then True else False)) with (fun st : state => ((snd st) m) <-> (if y then True else False)).
              replace (fun st : state => ((b !-> False; (snd st)) m) <-> (if y then True else False)) with (fun st : state => ((snd st) m) <-> (if y then True else False)).
              replace ((1 - 0.5)%R) with (0.5%R).
              unfold PAImplies.
              intro ps.
              replace (((0.5 * (fst ps (fun st : state => (snd st m) <-> (if y then True else False)))) +
    (0.5 * (fst ps (fun st : state => (snd st m) <-> (if y then True else False)))))%R) with (fst ps (fun st : state => (snd st m) <-> (if y then True else False))).
              replace (fun st : state =>
        (((snd st m) /\ (~ True)) \/ ((~ (snd st m)) /\ True)) <->
        ((if x then True else False) /\ ((snd st m) <-> (if y then True else False)))) with (fun st : state => ((~ (snd st m)) <-> ((if x then True else False) /\ ((snd st m) <-> (if y then True else False))))).
              replace (fun st : state =>
        ((((snd st m) /\ (~ False)) \/ ((~ (snd st m)) /\ False)) <-> (if x then True else False)) /\
        ((snd st m) <-> (if y then True else False))) with (fun st : state => ((snd st m) <-> (if x then True else False)) /\
        ((snd st m) <-> (if y then True else False))).
              replace (fun st : state =>
         (((snd st m) /\ (~ True)) \/ ((~ (snd st m)) /\ True)) <-> (if x then True else False)) with (fun st : state => (~ (snd st m)) <-> (if x then True else False)).
              replace (fun st : state =>
         (((snd st m) /\ (~ False)) \/ ((~ (snd st m)) /\ False)) <-> (if x then True else False)) with (fun st : state => (snd st m) <-> (if x then True else False)).
            replace (((0.5 *
    (fst ps
       (fun st : state =>
        ((((snd st m) /\ (~ True)) \/ ((~ (snd st m)) /\ True)) <-> (if x then True else False)) /\
        ((snd st m) <-> (if y then True else False))))) +
   (0.5 *
    (fst ps
       (fun st : state =>
        ((snd st m) <-> (if x then True else False)) /\ ((snd st m) <-> (if y then True else False))))))%R) with ((0.5 * (fst ps (fun st : state => (snd st m) <-> (if y then True else False))))%R).
        intro H. apply Rmult_eq_compat_r with (r := (fst ps (fun st : state => (snd st m) <-> (if y then True else False)))). rewrite Rmult_comm.
        replace ((0.5 * (fst ps (fun st : state => (snd st m) <-> (if x then True else False))))%R) with (((fst ps (fun st : state => (snd st m) <-> (if x then True else False))) * 0.5)%R).
        rewrite <- Rmult_plus_distr_r. replace (((fst ps (fun st : state => (~ (snd st m)) <-> (if x then True else False))) +
   (fst ps (fun st : state => (snd st m) <-> (if x then True else False))))%R) with (fst ps {{true}}). lra.
        rewrite measure_true_dest with (Q := (fun st : state => (~ (snd st m)) <-> (if x then True else False))). apply Rplus_eq_compat_l. apply equivalence. unfold Assertion_equiv. intro. tauto.
        apply Rmult_comm.
        replace ((0.5 *
   (fst ps
      (fun st : state =>
       ((((snd st m) /\ (~ True)) \/ ((~ (snd st m)) /\ True)) <-> (if x then True else False)) /\
       ((snd st m) <-> (if y then True else False)))))%R) with (((fst ps
      (fun st : state =>
       ((((snd st m) /\ (~ True)) \/ ((~ (snd st m)) /\ True)) <-> (if x then True else False)) /\
       ((snd st m) <-> (if y then True else False)))) * 0.5)%R).
        replace ((0.5 *
   (fst ps
      (fun st : state =>
       ((snd st m) <-> (if x then True else False)) /\ ((snd st m) <-> (if y then True else False)))))%R) with (((fst ps
      (fun st : state =>
       ((snd st m) <-> (if x then True else False)) /\ ((snd st m) <-> (if y then True else False)))) * 0.5)%R). rewrite <- Rmult_plus_distr_r. rewrite Rmult_comm. apply Rmult_eq_compat_r.
        rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro. tauto. tauto. apply Rmult_comm. apply Rmult_comm. apply functional_extensionality. intro. apply propositional_extensionality. tauto.
        apply functional_extensionality. intro. apply propositional_extensionality. tauto.
        apply functional_extensionality. intro. apply propositional_extensionality. tauto.
        apply functional_extensionality. intro. apply propositional_extensionality. tauto. lra. lra.
        apply functional_extensionality. intro. apply propositional_extensionality. tauto.
        apply functional_extensionality. intro. rewrite t_update_neq. apply propositional_extensionality. tauto. easy.
        apply functional_extensionality. intro. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. tauto. easy.
        apply functional_extensionality. intro. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. tauto. easy.
        apply functional_extensionality. intro. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. tauto. easy.
        apply functional_extensionality. intro. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. tauto. easy.
        - apply HBToss.
      + apply HConseqLeft with (eta2 := (basgn_pt c (<{((m /\ ~ b) \/ (~ m /\ b))}>) ({{(prob ((c <-> x) /\ (m <-> y))) = ((prob (c <-> x))*(prob (m <-> y)))}}))).
        - easy.
        - apply HBAsgn.
Qed.

Definition m1 : string := "m1".
Definition c1 : string := "c1".
Definition m2 : string := "m2".
Definition c2 : string := "c2".

Definition OneTimePad_2bit : Cmd :=
<{ 
  (b toss 0.5;
  c1 b= ((m1 /\ ~ b) \/ (~ m1 /\ b)));
  (b toss 0.5;
  c2 b= ((m2 /\ ~ b) \/ (~ m2 /\ b)))
}>.

Lemma second_bit : forall x1 x2 y1 y2 : bool, hoare_triple ({{(prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob (c1 <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2)))) }}) 
    (<{ b toss 0.5;
        c2 b= ((m2 /\ ~ b) \/ (~ m2 /\ b)) }>) ({{(prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob ((c1 <-> x1) /\ (c2 <-> x2)))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}}).
Proof. intros x1 x2 y1 y2. apply HSeq with (eta2 := ({{(prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2)))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}})).
        + apply HConseqLeft with (eta2 := (btoss_pt (b) (0.5%R) ({{(prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2)))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}}))).
          - uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. unfold PAImplies. intro ps.
              replace (fst ps
         (fun st : state =>
          (((b !-> True; (snd st)) c1) <-> (if x1 then True else False)) /\
          ((((((b !-> True; (snd st)) m2) /\ (~ ((b !-> True; (snd st)) b))) \/
             ((~ ((b !-> True; (snd st)) m2)) /\ ((b !-> True; (snd st)) b))) <->
            (if x2 then True else False)) /\
           ((((b !-> True; (snd st)) m1) <-> (if y1 then True else False)) /\
            (((b !-> True; (snd st)) m2) <-> (if y2 then True else False)))))) with (fst ps
         (fun st : state =>
          (((snd st) c1) <-> (if x1 then True else False)) /\
          (((((~ ((snd st) m2)))) <->
            (if x2 then True else False)) /\
           ((((snd st) m1) <-> (if y1 then True else False)) /\
            (((snd st) m2) <-> (if y2 then True else False)))))).
              replace (fst ps
       (fun st : state =>
        (((b !-> False; (snd st)) c1) <-> (if x1 then True else False)) /\
        ((((((b !-> False; (snd st)) m2) /\ (~ ((b !-> False; (snd st)) b))) \/
           ((~ ((b !-> False; (snd st)) m2)) /\ ((b !-> False; (snd st)) b))) <->
          (if x2 then True else False)) /\
         ((((b !-> False; (snd st)) m1) <-> (if y1 then True else False)) /\
          (((b !-> False; (snd st)) m2) <-> (if y2 then True else False)))))) with (fst ps
       (fun st : state =>
        (((snd st) c1) <-> (if x1 then True else False)) /\
        ((((((snd st) m2))) <->
          (if x2 then True else False)) /\
         ((((snd st) m1) <-> (if y1 then True else False)) /\
          (((snd st) m2) <-> (if y2 then True else False)))))). 
             replace (fst ps
        (fun st : state =>
         (((b !-> True; (snd st)) c1) <-> (if x1 then True else False)) /\
         (((((b !-> True; (snd st)) m2) /\ (~ ((b !-> True; (snd st)) b))) \/
           ((~ ((b !-> True; (snd st)) m2)) /\ ((b !-> True; (snd st)) b))) <->
          (if x2 then True else False)))) with (fst ps
        (fun st : state =>
         (((snd st) c1) <-> (if x1 then True else False)) /\
         ((((~ ((snd st) m2)))) <->
          (if x2 then True else False)))).
              replace (fst ps
        (fun st : state =>
         (((b !-> False; (snd st)) c1) <-> (if x1 then True else False)) /\
         (((((b !-> False; (snd st)) m2) /\ (~ ((b !-> False; (snd st)) b))) \/
           ((~ ((b !-> False; (snd st)) m2)) /\ ((b !-> False; (snd st)) b))) <->
          (if x2 then True else False)))) with (fst ps
        (fun st : state =>
         (((snd st) c1) <-> (if x1 then True else False)) /\
         (((((snd st) m2))) <->
          (if x2 then True else False)))).
              replace (fst ps
        (fun st : state =>
         (((b !-> True; (snd st)) m1) <-> (if y1 then True else False)) /\
         (((b !-> True; (snd st)) m2) <-> (if y2 then True else False)))) with (fst ps
        (fun st : state =>
         (((snd st) m1) <-> (if y1 then True else False)) /\
         (((snd st) m2) <-> (if y2 then True else False)))).
              replace (fst ps
        (fun st : state =>
         (((b !-> False; (snd st)) m1) <-> (if y1 then True else False)) /\
         (((b !-> False; (snd st)) m2) <-> (if y2 then True else False)))) with (fst ps
        (fun st : state =>
         (((snd st) m1) <-> (if y1 then True else False)) /\
         (((snd st) m2) <-> (if y2 then True else False)))).
              replace ((1 - 0.5)%R) with (0.5%R). intro H.
              replace (((0.5 *
    (fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False))))) +
   (0.5 *
    (fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False))))))%R) with (fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False)))).
        set (t1 := (fst ps
      (fun st : state =>
       ((snd st c1) <-> (if x1 then True else False)) /\
       (((~ (snd st m2)) <-> (if x2 then True else False)) /\
        (((snd st m1) <-> (if y1 then True else False)) /\
         ((snd st m2) <-> (if y2 then True else False))))))). 
        set (t2 := (fst ps
      (fun st : state =>
       ((snd st c1) <-> (if x1 then True else False)) /\
       (((snd st m2) <-> (if x2 then True else False)) /\
        (((snd st m1) <-> (if y1 then True else False)) /\
         ((snd st m2) <-> (if y2 then True else False))))))).
          replace (((0.5 * t1) + (0.5 * t2))%R) with (((t1 + t2)*(0.5))%R) by lra.
          set (t3 := (fst ps
       (fun st : state =>
        ((snd st c1) <-> (if x1 then True else False)) /\
        ((~ (snd st m2)) <-> (if x2 then True else False))))).
          set (t4 := (fst ps
       (fun st : state =>
        ((snd st c1) <-> (if x1 then True else False)) /\
        ((snd st m2) <-> (if x2 then True else False))))).
            set (t5 := (fst ps
     (fun st : state =>
      ((snd st m1) <-> (if y1 then True else False)) /\
      ((snd st m2) <-> (if y2 then True else False))))).
            replace ( ((((0.5 * t3) + (0.5 * t4)) * t5)%R)) with ((((t3 + t4)*t5)*0.5)%R) by lra.
            apply Rmult_eq_compat_r. replace ((t1 + t2)%R) with (fst ps
       (fun st : state =>
        ((snd st c1) <-> (if x1 then True else False)) /\
        (((snd st m1) <-> (if y1 then True else False)) /\
         ((snd st m2) <-> (if y2 then True else False))))).
            replace ((t3 + t4)%R) with (fst ps (fun st : state => (snd st c1) <-> (if x1 then True else False))). revert t5.
            simpl. apply H. revert t3 t4. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st.
            tauto. intro st. tauto.
            revert t1 t2. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st.
            tauto. intro st. tauto. lra. lra. 
            apply equivalence. unfold Assertion_equiv. intro st. tauto.
            apply equivalence. unfold Assertion_equiv. intro st. tauto.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. tauto.
            easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. tauto.
            easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. tauto.
            easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. tauto.
            easy. easy.
        - apply HBToss.
      + apply HConseqLeft with (eta2 := (basgn_pt c2 (<{((m2 /\ ~ b) \/ (~ m2 /\ b))}>) ({{(prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob ((c1 <-> x1) /\ (c2 <-> x2)))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}}))).
        - easy.
        - apply HBAsgn.
Qed.

Lemma first_bit : forall x1 x2 y1 y2 : bool, hoare_triple ({{(prob true) = 1}}) <{ 
  b toss 0.5;
  c1 b= ((m1 /\ ~ b) \/ (~ m1 /\ b))}> ({{(prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob (c1 <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2)))) }}).
Proof. intros x1 x2 y1 y2. apply HSeq with (eta2 := ({{(prob ((((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob (((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}})).
        + apply HConseqLeft with (eta2 := (btoss_pt (b) (0.5%R) ({{(prob ((((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob (((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}}))).
          - uncoerce_basic. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. unfold PAImplies. intro ps. intro H.
              replace (fst ps
      (fun st : state =>
       (((((b !-> True; (snd st)) m1) /\ (~ ((b !-> True; (snd st)) b))) \/
         ((~ ((b !-> True; (snd st)) m1)) /\ ((b !-> True; (snd st)) b))) <->
        (if x1 then True else False)) /\
       ((((b !-> True; (snd st)) m1) <-> (if y1 then True else False)) /\
        (((b !-> True; (snd st)) m2) <-> (if y2 then True else False))))) with (fst ps
      (fun st : state =>
       (((
         ((~ ((snd st) m1)))) <->
        (if x1 then True else False)) /\
       ((((snd st) m1) <-> (if y1 then True else False)) /\
        (((snd st) m2) <-> (if y2 then True else False)))))).
              replace (fst ps
      (fun st : state =>
       (((((b !-> False; (snd st)) m1) /\ (~ ((b !-> False; (snd st)) b))) \/
         ((~ ((b !-> False; (snd st)) m1)) /\ ((b !-> False; (snd st)) b))) <->
        (if x1 then True else False)) /\
       ((((b !-> False; (snd st)) m1) <-> (if y1 then True else False)) /\
        (((b !-> False; (snd st)) m2) <-> (if y2 then True else False))))) with (fst ps
      (fun st : state =>
       (((((snd st) m1))) <->
        (if x1 then True else False)) /\
       ((((snd st) m1) <-> (if y1 then True else False)) /\
        (((snd st) m2) <-> (if y2 then True else False))))). 
             replace (fst ps
       (fun st : state =>
        ((((b !-> True; (snd st)) m1) /\ (~ ((b !-> True; (snd st)) b))) \/
         ((~ ((b !-> True; (snd st)) m1)) /\ ((b !-> True; (snd st)) b))) <->
        (if x1 then True else False))) with (fst ps
       (fun st : state =>
        (((~ ((snd st) m1)))) <->
        (if x1 then True else False))).
              replace (fst ps
       (fun st : state =>
        ((((b !-> False; (snd st)) m1) /\ (~ ((b !-> False; (snd st)) b))) \/
         ((~ ((b !-> False; (snd st)) m1)) /\ ((b !-> False; (snd st)) b))) <->
        (if x1 then True else False))) with (fst ps
       (fun st : state =>
        ((((snd st) m1))) <->
        (if x1 then True else False))).
              replace (fst ps
       (fun st : state =>
        (((b !-> True; (snd st)) m1) <-> (if y1 then True else False)) /\
        (((b !-> True; (snd st)) m2) <-> (if y2 then True else False)))) with (fst ps
       (fun st : state =>
        (((snd st) m1) <-> (if y1 then True else False)) /\
        (((snd st) m2) <-> (if y2 then True else False)))).
              replace (fst ps
       (fun st : state =>
        (((b !-> False; (snd st)) m1) <-> (if y1 then True else False)) /\
        (((b !-> False; (snd st)) m2) <-> (if y2 then True else False)))) with (fst ps
       (fun st : state =>
        (((snd st) m1) <-> (if y1 then True else False)) /\
        (((snd st) m2) <-> (if y2 then True else False)))).
              replace ((1 - 0.5)%R) with (0.5%R).
            replace (((0.5 *
    (fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False))))) +
   (0.5 *
    (fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False))))))%R) with ((fst ps
       (fun st : state =>
        ((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False))))) by lra.
            set (t1 := (fst ps
      (fun st : state =>
       ((~ (snd st m1)) <-> (if x1 then True else False)) /\
       (((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False)))))).
            set (t2 := (fst ps
      (fun st : state =>
       ((snd st m1) <-> (if x1 then True else False)) /\
       (((snd st m1) <-> (if y1 then True else False)) /\
        ((snd st m2) <-> (if y2 then True else False)))))).
            set (t3 := (fst ps (fun st : state => (~ (snd st m1)) <-> (if x1 then True else False)))).
            set (t4 := (fst ps (fun st : state => (snd st m1) <-> (if x1 then True else False)))).
            set (t5 := (fst ps
     (fun st : state =>
      ((snd st m1) <-> (if y1 then True else False)) /\
      ((snd st m2) <-> (if y2 then True else False))))).
            replace (((0.5 * t1) + (0.5 * t2))%R) with (((t1 + t2)*(0.5))%R) by lra.
            replace ((((0.5 * t3) + (0.5 * t4)) * t5)%R) with ((((t3 + t4)*t5)*0.5)%R) by lra. apply Rmult_eq_compat_r.
            replace ((t1 + t2)%R) with ((1 * t5)%R). apply Rmult_eq_compat_r. symmetry. replace ((t3 + t4)%R) with (fst ps {{true}}). apply H.
            revert t3 t4. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st. tauto.
            intro st. tauto. replace ((1 * t5)%R) with (t5) by lra. revert t5 t1 t2. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st. tauto.
            intro st. tauto. lra. 
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. tauto. easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. tauto. easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. tauto. easy. 
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. tauto. easy. 
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_neq. tauto. easy. easy.
            apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_neq.  tauto. easy. easy.  
          - apply HBToss.
      + apply HConseqLeft with (eta2 := (basgn_pt c1 (<{((m1 /\ ~ b) \/ (~ m1 /\ b))}>) ({{(prob ((c1 <-> x1) /\ ((m1 <-> y1) /\ (m2 <-> y2)))) = ((prob (c1 <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2)))) }}))).
        - easy. 
        - apply HBAsgn.
Qed.  

Theorem OTP2bit_Input_Indep : forall x1 x2 y1 y2 : bool, hoare_triple ({{(prob true) = 1}}) OneTimePad_2bit ({{(prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob ((c1 <-> x1) /\ (c2 <-> x2)))*(prob ((m1 <-> y1) /\ (m2 <-> y2))))}}).
Proof. intros x1 x2 y1 y2. apply HSeq with (eta2 := ({{(prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2))) = ((prob (c1 <-> x1))*(prob ((m1 <-> y1) /\ (m2 <-> y2)))) }})).
        + apply first_bit. easy.
        + apply second_bit.
Qed. 

End OTP.
