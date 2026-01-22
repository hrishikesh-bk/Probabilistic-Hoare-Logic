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

Module OT.

(* A formal proof that the bits received by the sender from the trusted third party in an 
oblivious transfer scheme is independent of the choice bit of the receiver. In the following,
c is the choice bit of the receiver, r0,r1 and e are sent to the sender by the trusted third
party. 
*)

Definition r0 : string := "r0".
Definition r1 : string := "r1".
Definition c : string := "c".
Definition d : string := "d".
Definition e : string := "e".

Definition ObliviousTransfer : Cmd :=
<{
  r0 toss 0.5;
  r1 toss 0.5;
  d toss 0.5;
  e b= ((c /\ ~ d) \/ (~ c /\ d))
}>.

Theorem OT_Input_Indep : forall w x y z : bool, hoare_triple ({{ (prob (true)) = 1 }}) 
                          ObliviousTransfer ({{(prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) = ((prob (c <-> w))*(prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))))}}).
Proof. intros w x y z. apply HSeq with (eta2 := {{(prob ((c <-> w) /\ (r0 <-> x))) = ((prob (c <-> w))*(prob (r0 <-> x)))}}).
        + apply HConseqLeft with (eta2 := (btoss_pt r0 (0.5)%R ({{(prob ((c <-> w) /\ (r0 <-> x))) = ((prob (c <-> w))*(prob (r0 <-> x)))}}))).
          - unfold PAImplies. intro ps. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            replace (1 - 0.5)%R with (0.5)%R by lra.
            replace (fst ps
       (fun st : state =>
        (((r0 !-> True; (snd st)) c) <-> (if w then True else False)) /\
        (((r0 !-> True; (snd st)) r0) <-> (if x then True else False)))) with (fst ps
       (fun st : state =>
        (((snd st) c) <-> (if w then True else False)) /\
        (True <-> (if x then True else False)))).
          replace (fst ps
       (fun st : state =>
        (((r0 !-> False; (snd st)) c) <-> (if w then True else False)) /\
        (((r0 !-> False; (snd st)) r0) <-> (if x then True else False)))) with (fst ps
       (fun st : state =>
        (((snd st) c) <-> (if w then True else False)) /\
        (False <-> (if x then True else False)))).
          replace (fst ps (fun st : state => ((r0 !-> True; (snd st)) c) <-> (if w then True else False))) with (fst ps (fun st : state => ((snd st) c) <-> (if w then True else False))).
          replace (fst ps (fun st : state => ((r0 !-> False; (snd st)) c) <-> (if w then True else False))) with (fst ps (fun st : state => ((snd st) c) <-> (if w then True else False))).
          replace (fst ps (fun st : state => ((r0 !-> True; (snd st)) r0) <-> (if x then True else False))) with (fst ps (fun st : state => True <-> (if x then True else False))).
          replace (fst ps (fun st : state => ((r0 !-> False; (snd st)) r0) <-> (if x then True else False))) with (fst ps (fun st : state => False <-> (if x then True else False))).
          set (t1 := (fst ps
       (fun st : state =>
        ((snd st c) <-> (if w then True else False)) /\ (True <-> (if x then True else False))))).
          set (t2 := (fst ps
       (fun st : state =>
        ((snd st c) <-> (if w then True else False)) /\ (False <-> (if x then True else False))))).
          set (t3 := (fst ps (fun st : state => (snd st c) <-> (if w then True else False)))).
          set (t4 := (fst ps (fun st : state => (snd st c) <-> (if w then True else False)))).
          set (t5 := (fst ps (fun _ : state => True <-> (if x then True else False)))).
          set (t6 := (fst ps (fun _ : state => False <-> (if x then True else False)))).
          intro H.
          replace (((0.5 * t1) + (0.5 * t2))%R) with ((t1 + t2)*0.5)%R by lra.
          replace ((0.5 * t5) + (0.5 * t6))%R with ((t5 + t6)*0.5)%R by lra.
          replace ((0.5 * t3) + (0.5 * t3))%R with (t3) by lra.
          replace (t3 * ((t5 + t6) * 0.5))%R with (( (t5 + t6) * t3) * 0.5)%R by lra. apply Rmult_eq_compat_r.
          replace (t1 + t2)%R with (1 * t3)%R. apply Rmult_eq_compat_r.
          revert t5 t6. simpl. rewrite fin_additivity. rewrite <- H. apply equivalence. unfold Assertion_equiv. intro st. tauto. intro st. tauto.
          replace (1 * t3)%R with t3 by lra. revert t1 t2 t3. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st. tauto. intro st. tauto.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_eq. tauto.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
         - apply HBToss.
        + apply HSeq with (eta2 := {{(prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y))) = ((prob (c <-> w))*(prob ((r0 <-> x) /\ (r1 <-> y))))}}).
          - apply HConseqLeft with (eta2 := (btoss_pt r1 (0.5)%R ({{(prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y))) = ((prob (c <-> w))*(prob ((r0 <-> x) /\ (r1 <-> y))))}}))).
            * unfold PAImplies. intro st. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic.
            replace (1 - 0.5)%R with (0.5)%R by lra.
            replace (fst st
       (fun st0 : state =>
        (((r1 !-> True; (snd st0)) c) <-> (if w then True else False)) /\
        ((((r1 !-> True; (snd st0)) r0) <-> (if x then True else False)) /\
         (((r1 !-> True; (snd st0)) r1) <-> (if y then True else False))))) with (fst st
       (fun st0 : state =>
        (((snd st0) c) <-> (if w then True else False)) /\
        ((((snd st0) r0) <-> (if x then True else False)) /\
         (True <-> (if y then True else False))))).
          replace (fst st
       (fun st0 : state =>
        (((r1 !-> False; (snd st0)) c) <-> (if w then True else False)) /\
        ((((r1 !-> False; (snd st0)) r0) <-> (if x then True else False)) /\
         (((r1 !-> False; (snd st0)) r1) <-> (if y then True else False))))) with (fst st
       (fun st0 : state =>
        (((snd st0) c) <-> (if w then True else False)) /\
        ((((snd st0) r0) <-> (if x then True else False)) /\
         (False <-> (if y then True else False))))).
          replace (fst st (fun st0 : state => ((r1 !-> True; (snd st0)) c) <-> (if w then True else False))) with (fst st (fun st0 : state => ((snd st0) c) <-> (if w then True else False))).
          replace (fst st (fun st0 : state => ((r1 !-> False; (snd st0)) c) <-> (if w then True else False))) with (fst st (fun st0 : state => ((snd st0) c) <-> (if w then True else False))).
          replace (fst st
        (fun st0 : state =>
         (((r1 !-> True; (snd st0)) r0) <-> (if x then True else False)) /\
         (((r1 !-> True; (snd st0)) r1) <-> (if y then True else False)))) with (fst st
        (fun st0 : state =>
         (((snd st0) r0) <-> (if x then True else False)) /\
         (True <-> (if y then True else False)))).
          replace (fst st
        (fun st0 : state =>
         (((r1 !-> False; (snd st0)) r0) <-> (if x then True else False)) /\
         (((r1 !-> False; (snd st0)) r1) <-> (if y then True else False)))) with (fst st
        (fun st0 : state =>
         (((snd st0) r0) <-> (if x then True else False)) /\
         (False <-> (if y then True else False)))).
          set (t1 := (fst st
       (fun st0 : state =>
        ((snd st0 c) <-> (if w then True else False)) /\
        (((snd st0 r0) <-> (if x then True else False)) /\ (True <-> (if y then True else False)))))).
          set (t2 := (fst st
       (fun st0 : state =>
        ((snd st0 c) <-> (if w then True else False)) /\
        (((snd st0 r0) <-> (if x then True else False)) /\ (False <-> (if y then True else False)))))).
          set (t3 := (fst st (fun st0 : state => (snd st0 c) <-> (if w then True else False)))).
          set (t4 := (fst st (fun st0 : state => (snd st0 c) <-> (if w then True else False)))).
          set (t5 := (fst st
        (fun st0 : state =>
         ((snd st0 r0) <-> (if x then True else False)) /\ (True <-> (if y then True else False))))).
          set (t6 := (fst st
        (fun st0 : state =>
         ((snd st0 r0) <-> (if x then True else False)) /\ (False <-> (if y then True else False))))).
          intro H.
          replace (((0.5 * t1) + (0.5 * t2))%R) with ((t1 + t2)*0.5)%R by lra.
          replace ((0.5 * t5) + (0.5 * t6))%R with ((t5 + t6)*0.5)%R by lra.
          replace ((0.5 * t3) + (0.5 * t3))%R with (t3) by lra.
          replace (t3 * ((t5 + t6) * 0.5))%R with (( t3 * (t5 + t6) ) * 0.5)%R by lra. apply Rmult_eq_compat_r.
          replace (t1 + t2)%R with (fst st
       (fun st : state =>
        ((snd st c) <-> (if w then True else False)) /\
        ((snd st r0) <-> (if x then True else False)))).
          replace (t5 + t6)%R with (fst st (fun st : state => (snd st r0) <-> (if x then True else False))).
          apply H.
          revert t5 t6. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st0. tauto. intro st0. tauto.
          revert t1 t2. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st0. tauto. intro st0. tauto.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_eq. tauto.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_eq. tauto.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st0. rewrite t_update_neq. rewrite t_update_eq. tauto. easy.
          * apply HBToss.
        - apply HSeq with (eta2 := (basgn_pt e <{ ((c /\ ~ d) \/ (~ c /\ d))}> ({{(prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) = ((prob (c <-> w))*(prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))))}}))).
          * apply HConseqLeft with (eta2 := (btoss_pt d (0.5)%R (basgn_pt e (<{ ((c /\ ~ d) \/ (~ c /\ d))}>) ({{(prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) = ((prob (c <-> w))*(prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))))}})))).
            ** unfold PAImplies. intro ps. unfold btoss_pt. unfold basgn_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. intro H.
                replace (fst ps
      (fun st : state =>
       (((e
          !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
              ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d)); 
          (d !-> True; (snd st))) c) <-> (if w then True else False)) /\
       ((((e
           !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
               ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
           (d !-> True; (snd st))) r0) <-> (if x then True else False)) /\
        ((((e
            !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
                ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
            (d !-> True; (snd st))) r1) <-> (if y then True else False)) /\
         (((e
            !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
                ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
            (d !-> True; (snd st))) e) <-> (if z then True else False)))))) with (fst ps
      (fun st : state =>
       (((snd st) c) <-> (if w then True else False)) /\
       ((((snd st) r0) <-> (if x then True else False)) /\
        ((((snd st) r1) <-> (if y then True else False)) /\
         (((  ((~ ((snd st) c)))) <-> (if z then True else False))))))).
          replace (fst ps
      (fun st : state =>
       (((e
          !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
              ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
          (d !-> False; (snd st))) c) <-> (if w then True else False)) /\
       ((((e
           !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
               ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
           (d !-> False; (snd st))) r0) <-> (if x then True else False)) /\
        ((((e
            !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
                ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
            (d !-> False; (snd st))) r1) <-> (if y then True else False)) /\
         (((e
            !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
                ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
            (d !-> False; (snd st))) e) <-> (if z then True else False)))))) with (fst ps
      (fun st : state =>
       (((snd st) c) <-> (if w then True else False)) /\
       ((((snd st) r0) <-> (if x then True else False)) /\
        ((((snd st) r1) <-> (if y then True else False)) /\
         (((((snd st) c) <-> (if z then True else False)))))))).
        replace (fst ps
       (fun st : state =>
        ((e
          !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
              ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d)); 
          (d !-> True; (snd st))) c) <-> (if w then True else False))) with (fst ps
       (fun st : state =>
        ((snd st) c) <-> (if w then True else False))).
        replace (fst ps
       (fun st : state =>
        ((e
          !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
              ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
          (d !-> False; (snd st))) c) <-> (if w then True else False))) with (fst ps
       (fun st : state =>
        ((snd st) c) <-> (if w then True else False))).
          replace (fst ps
       (fun st : state =>
        (((e
           !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
               ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
           (d !-> True; (snd st))) r0) <-> (if x then True else False)) /\
        ((((e
            !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
                ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
            (d !-> True; (snd st))) r1) <-> (if y then True else False)) /\
         (((e
            !-> (((d !-> True; (snd st)) c) /\ (~ ((d !-> True; (snd st)) d))) \/
                ((~ ((d !-> True; (snd st)) c)) /\ ((d !-> True; (snd st)) d));
            (d !-> True; (snd st))) e) <-> (if z then True else False))))) with (fst ps
       (fun st : state =>
        (((snd st) r0) <-> (if x then True else False)) /\
        ((((snd st) r1) <-> (if y then True else False)) /\
         (( ((~ ((snd st) c)))) <-> (if z then True else False))))).
          replace (fst ps
       (fun st : state =>
        (((e
           !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
               ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
           (d !-> False; (snd st))) r0) <-> (if x then True else False)) /\
        ((((e
            !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
                ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
            (d !-> False; (snd st))) r1) <-> (if y then True else False)) /\
         (((e
            !-> (((d !-> False; (snd st)) c) /\ (~ ((d !-> False; (snd st)) d))) \/
                ((~ ((d !-> False; (snd st)) c)) /\ ((d !-> False; (snd st)) d));
            (d !-> False; (snd st))) e) <-> (if z then True else False))))) with (fst ps
       (fun st : state =>
        (((snd st) r0) <-> (if x then True else False)) /\
        ((((snd st) r1) <-> (if y then True else False)) /\
         (((((snd st) c))) <-> (if z then True else False))))).
          set (t1 := (fst ps
      (fun st : state =>
       ((snd st c) <-> (if w then True else False)) /\
       (((snd st r0) <-> (if x then True else False)) /\
        (((snd st r1) <-> (if y then True else False)) /\
         ((~ (snd st c)) <-> (if z then True else False))))))).
          set (t2 := (fst ps
      (fun st : state =>
       ((snd st c) <-> (if w then True else False)) /\
       (((snd st r0) <-> (if x then True else False)) /\
        (((snd st r1) <-> (if y then True else False)) /\
         ((snd st c) <-> (if z then True else False))))))). 
          set (t3 := (fst ps (fun st : state => (snd st c) <-> (if w then True else False)))). 
          set (t4 := (fst ps (fun st : state => (snd st c) <-> (if w then True else False)))). 
          set (t5 := (fst ps
       (fun st : state =>
        ((snd st r0) <-> (if x then True else False)) /\
        (((snd st r1) <-> (if y then True else False)) /\
         ((~ (snd st c)) <-> (if z then True else False)))))). 
          set (t6 := (fst ps
       (fun st : state =>
        ((snd st r0) <-> (if x then True else False)) /\
        (((snd st r1) <-> (if y then True else False)) /\
         ((snd st c) <-> (if z then True else False)))))).
          replace (1 - 0.5)%R with 0.5%R by lra.
          replace (((0.5 * t1) + (0.5 * t2))%R) with ((t1 + t2)*0.5)%R by lra.
          replace ((0.5 * t5) + (0.5 * t6))%R with ((t5 + t6)*0.5)%R by lra.
          replace ((0.5 * t3) + (0.5 * t3))%R with (t3) by lra.
          replace (t3 * ((t5 + t6) * 0.5))%R with (( t3 * (t5 + t6) ) * 0.5)%R by lra. apply Rmult_eq_compat_r.
          replace (t1 + t2)%R with (fst ps
       (fun st : state =>
        ((snd st c) <-> (if w then True else False)) /\
        (((snd st r0) <-> (if x then True else False)) /\
         ((snd st r1) <-> (if y then True else False))))).
          replace (t5 + t6)%R with (fst ps
         (fun st : state =>
          ((snd st r0) <-> (if x then True else False)) /\
          ((snd st r1) <-> (if y then True else False)))).
          apply H.
          revert t5 t6. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st. tauto. intro st. tauto.
          revert t1 t2. simpl. rewrite fin_additivity. apply equivalence. unfold Assertion_equiv. intro st. tauto. intro st. tauto.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_eq. tauto.
          easy. easy. easy. easy. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_eq. tauto.
          easy. easy. easy. easy. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. tauto. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_eq. tauto.
          easy. easy. easy. easy. easy. easy.
          apply equivalence. unfold Assertion_equiv. intro st. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. rewrite t_update_eq. tauto.
          easy. easy. easy. easy. easy. easy.
          ** apply HBToss.
          * apply HBAsgn.
Qed.  

 

End OT.
