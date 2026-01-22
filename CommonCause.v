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


Definition CommonCause (x y z a b: string): Cmd:=
<{
(x toss ((1/2)%R)); (y toss ((1/2)%R)); (z toss ((1/2)%R));
(a b= (x \/ z)); (b b= (y \/ z))
}>.


(* Strings *)
Definition x:string := "x". 
Definition y:string := "y". 
Definition z:string := "z". 
Definition a:string := "a". 
Definition b:string := "b". 

Definition hf := (1/2)%R.
Definition fth := (1/4)%R.
Definition eth := (1/8)%R.


Lemma TImp (P : Prop) :
  (iff True P) = P.
Proof.
  apply propositional_extensionality.
  tauto.
Qed.
Lemma FImp (P : Prop) :
  (iff False P) = ~P.
Proof.
  apply propositional_extensionality.
  tauto.
Qed.

Theorem CommonCauseCondIndep: forall (k1 k2 k3 : bool), {{ (prob true) = 1 }}
<{
(x toss ((1/2)%R)); (y toss ((1/2)%R)); (z toss ((1/2)%R));
(a b= (x \/ z)); (b b= (y \/ z))
}>
{{ ((prob ((a <-> k1) /\ (b <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob ((a <-> k1) /\ (z <-> k3)))* (prob ((b <-> k2) /\ (z <-> k3)))) }}.
Proof.
intros.
eapply HConseqLeft with (eta2 :=
{{   (hf * (prob (k1 /\ k2 /\ k3)) + (eth * (prob (~ k3)))) * ( hf * (prob true) ) 
     =
      ( ( (hf * (prob (k1 /\ k3))) + (fth * (prob (~ k3)))) * ( (hf * (prob (k2 /\ k3))) + (fth * (prob (~ k3)))) )
}}
).
- unfold PAImplies. intros. destruct k3.
   -- replace (fun st : state => ~ CBoolexp_of_bexp <{ true }> st) with (fun st : state => CBoolexp_of_bexp <{ false }> st).
      replace (Pteval (Pint (fun st : state => CBoolexp_of_bexp <{ false }> st)) ps) 
           with 0%R. unfold hf. unfold eth. unfold fth. rewrite H. ring_simplify. destruct k1.
       --- destruct k2. replace (fun st : state =>
       CBoolexp_of_bexp <{ true }> st /\
       CBoolexp_of_bexp <{ true }> st /\ CBoolexp_of_bexp <{ true }> st) with (fun st : state =>
       CBoolexp_of_bexp <{ true }> st). replace (fun st : state =>
       CBoolexp_of_bexp <{ true }> st /\ CBoolexp_of_bexp <{ true }> st) with (fun st : state =>
       CBoolexp_of_bexp <{ true }> st).  simpl. unfold PTerm_of_R. simpl in H. unfold PTerm_of_R in H. rewrite H. lra.
       apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       replace (fun st : state =>
       CBoolexp_of_bexp <{ true }> st /\
       CBoolexp_of_bexp <{ false }> st /\ CBoolexp_of_bexp <{ true }> st) with 
       (fun st : state =>
       CBoolexp_of_bexp <{ false }> st). replace (fun st : state =>
       CBoolexp_of_bexp <{ false }> st /\ CBoolexp_of_bexp <{ true }> st) with (fun st : state =>
       CBoolexp_of_bexp <{ false }> st). replace (Pteval (Pint (fun st : state => CBoolexp_of_bexp <{ false }> st)) ps) with 0%R.
       lra. apply eq_sym. apply measure_false_is_zero. apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       --- replace (fun st : state =>
       CBoolexp_of_bexp <{ false }> st /\
       CBoolexp_of_bexp (BConst k2) st /\ CBoolexp_of_bexp <{ true }> st) with (fun st : state =>
       CBoolexp_of_bexp <{ false }> st). replace (fun st : state =>
       CBoolexp_of_bexp <{ false }> st /\ CBoolexp_of_bexp <{ true }> st) with (fun st : state =>
       CBoolexp_of_bexp <{ false }> st). replace (Pteval (Pint (fun st : state => CBoolexp_of_bexp <{ false }> st)) ps) with 0%R.
       lra. apply eq_sym. apply measure_false_is_zero. apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
       --- apply eq_sym. apply measure_false_is_zero. 
       --- apply functional_extensionality. intros. apply propositional_extensionality. simpl. easy.
   -- replace (Pint
       (fun st : state =>
        CBoolexp_of_bexp (BConst k1) st /\
        CBoolexp_of_bexp (BConst k2) st /\ CBoolexp_of_bexp <{ false }> st)) with (Pint
       (fun st : state =>
        CBoolexp_of_bexp <{ false }> st)).
       replace  (fun st : state =>
        CBoolexp_of_bexp (BConst k1) st /\ CBoolexp_of_bexp <{ false }> st) with 
         (fun st : state =>
        CBoolexp_of_bexp <{ false }> st).
       replace (fun st : state =>
        CBoolexp_of_bexp (BConst k2) st /\ CBoolexp_of_bexp <{ false }> st) with (fun st : state =>
        CBoolexp_of_bexp <{ false }> st).
      replace (Pteval (Pint (fun st : state => CBoolexp_of_bexp <{ false }> st)) ps) 
           with 0%R.
      replace (fun st : state => ~ CBoolexp_of_bexp <{ false }> st) with (fun st : state => CBoolexp_of_bexp <{ true }> st).
      replace (Pteval (Pint (fun st : state => CBoolexp_of_bexp <{ true }> st)) ps ) with 1%R.
      replace (Pteval (Pint {{true}}) ps) with 1%R.      
      --- unfold PTerm_of_R. unfold hf. unfold eth. unfold fth. lra.
      --- apply functional_extensionality. intros. unfold CBoolexp_of_bexp. apply propositional_extensionality. easy.
      --- apply eq_sym. apply measure_false_is_zero.
      --- apply functional_extensionality. intros. apply propositional_extensionality. easy.
      --- apply functional_extensionality. intros. apply propositional_extensionality. easy.
      --- replace (fun st : state =>
   CBoolexp_of_bexp (BConst k1) st /\
   CBoolexp_of_bexp (BConst k2) st /\ CBoolexp_of_bexp <{ false }> st) with 
    (fun st : state => CBoolexp_of_bexp <{ false }> st). easy. apply functional_extensionality. intros. apply propositional_extensionality. easy.

- eapply HSeq with (eta2 := {{
 (((hf * (prob (k1 /\ k2 /\ k3))) + (fth * (prob (((x <-> k1) /\ (~k3))))) ) * (hf * (prob true)))
 = ( ((hf * (prob (k1 /\ k3))) + (hf * (prob ((x <-> k1) /\ (~k3))))) * ((hf * (prob (k2 /\ k3))) + (fth * (prob (~k3))))) 
}}).

-- eapply HConseqLeft with (eta2 := (btoss_pt x ((1/2)%R) {{
 (((hf * (prob (k1 /\ k2 /\ k3))) + (fth * (prob (((x <-> k1) /\ (~k3))))) ) * (hf * (prob true)))
 = ( ((hf * (prob (k1 /\ k3))) + (hf * (prob ((x <-> k1) /\ (~k3))))) * ((hf * (prob (k2 /\ k3))) + (fth * (prob (~k3))))) 
}})).
  * unfold hf. unfold fth. unfold eth. unfold PAImplies. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Pteval.
   intros. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. unfold Pteval.
    replace (1-1/2)%R with (1/2)%R by lra. simpl. unfold t_update. simpl.
    replace (1 / 2 *
   fst ps
     (fun _ : state =>
      (True <-> (if k1 then True else False)) /\
      ~ (if k3 then True else False)) +
   1 / 2 *
   fst ps
     (fun _ : state =>
      (False <-> (if k1 then True else False)) /\
      ~ (if k3 then True else False)))%R with ((1/2) * (fst ps (fun _ : state => ~ (if k3 then True else False))))%R.
   lra. 
   apply (Rmult_eq_reg_l 2). field_simplify.
   pose proof (measure_AnotB (fst ps) (fun st : state => ~ (if k3 then True else False))
            (fun st : state => (True <-> (if k1 then True else False)))) as mab. simpl in mab. unfold assert_of_Prop in mab.
  replace (False <-> (if k1 then True else False)) with (~(True <-> (if k1 then True else False))) by (apply propositional_extensionality; tauto).
  replace ((True <-> (if k1 then True else False)) /\ ~ (if k3 then True else False)) with 
          ((~ (if k3 then True else False)) /\ (True <-> (if k1 then True else False))) by (apply propositional_extensionality; tauto).
  replace ( ~ (True <-> (if k1 then True else False)) /\ ~ (if k3 then True else False) ) with 
       ( ~ (if k3 then True else False)  /\   ~ (True <-> (if k1 then True else False))) by (apply propositional_extensionality; tauto).
  lra. easy.
    
  

 * apply HBToss.
  -- eapply HSeq with (eta2 := {{
       (((hf * (prob (k1 /\ k2 /\ k3))) + (hf * (prob ( (x <-> k1) /\ (y <-> k2) /\ (~k3))))) * (hf * (prob true))) 
     = ( ((hf * (prob (k1 /\ k3))) + (hf * (prob ((x <-> k1) /\ (~k3))))) * ((hf * (prob (k2 /\ k3))) + (hf * (prob ((y <-> k2) /\ (~k3))))) )
}}).
 --- eapply HConseqLeft with (eta2 := (btoss_pt y ((1/2)%R) {{
       (((hf * (prob (k1 /\ k2 /\ k3))) + (hf * (prob ( (x <-> k1) /\ (y <-> k2) /\ (~k3))))) * (hf * (prob true))) 
     = ( ((hf * (prob (k1 /\ k3))) + (hf * (prob ((x <-> k1) /\ (~k3))))) * ((hf * (prob (k2 /\ k3))) + (hf * (prob ((y <-> k2) /\ (~k3))))) )
}})).
  * unfold hf. unfold fth. unfold PAImplies. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Pteval.
   intros. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. unfold Pteval.
    replace (1-1/2)%R with (1/2)%R by lra. simpl. unfold t_update. simpl.
    replace (1/2 * (1 / 2 *
   fst ps
     (fun st : state =>
      (snd st x <-> (if k1 then True else False)) /\
      (True <-> (if k2 then True else False)) /\
      ~ (if k3 then True else False)) +
   1 / 2 *
   fst ps
     (fun st : state =>
      (snd st x <-> (if k1 then True else False)) /\
      (False <-> (if k2 then True else False)) /\
      ~ (if k3 then True else False))))%R with
      (1/4 * fst ps (fun st : state =>
         (snd st x <-> (if k1 then True else False)) /\
         ~ (if k3 then True else False)))%R.
  replace ( 1 / 2 * (1 / 2 *
   fst ps
     (fun _ : state =>
      (True <-> (if k2 then True else False)) /\
      ~ (if k3 then True else False)) +
   1 / 2 *
   fst ps
     (fun _ : state =>
      (False <-> (if k2 then True else False)) /\
      ~ (if k3 then True else False))))%R with (1 / 4 * fst ps (fun _ : state => ~ (if k3 then True else False)))%R.
  lra.
 apply (Rmult_eq_reg_l 4). field_simplify.
 pose proof (measure_AnotB (fst ps) (~ (if k3 then True else False))  (True <-> (if k2 then True else False))) as mab.
 simpl in mab. unfold assert_of_Prop in mab. replace
    ((True <-> (if k2 then True else False)) /\
    ~ (if k3 then True else False)) with (
         (~ (if k3 then True else False)) /\
         (True <-> (if k2 then True else False))).
  replace ((False <-> (if k2 then True else False)) /\
    ~ (if k3 then True else False)) with ((~ (if k3 then True else False)) /\ ~(True <-> (if k2 then True else False))).
  lra.
  apply propositional_extensionality. tauto. apply propositional_extensionality. tauto. easy.
 apply (Rmult_eq_reg_l 4). field_simplify.
 pose proof (measure_AnotB (fst ps) (fun st : state => ((snd st x <-> (if k1 then True else False)) /\ ~ (if k3 then True else False)))
            (fun st : state => (True <-> (if k2 then True else False)))) as mab. simpl in mab. unfold assert_of_Prop in mab.
 replace (fun st : state =>
    (snd st x <-> (if k1 then True else False)) /\
    (True <-> (if k2 then True else False)) /\
    ~ (if k3 then True else False))
  with (fun st : state =>
          ((snd st x <-> (if k1 then True else False)) /\
           ~ (if k3 then True else False)) /\
          (True <-> (if k2 then True else False))).
 replace (fun st : state =>
    (snd st x <-> (if k1 then True else False)) /\
    (False <-> (if k2 then True else False)) /\
    ~ (if k3 then True else False))
  with (fun st : state =>
         ((snd st x <-> (if k1 then True else False)) /\
          ~ (if k3 then True else False)) /\
         ~ (True <-> (if k2 then True else False))).
  lra. apply functional_extensionality. intros. apply propositional_extensionality. tauto. 
  apply functional_extensionality. intros. apply propositional_extensionality. tauto.  easy.
  * apply HBToss.
(* Seq:  a <- x \/ z *)
  --- eapply HSeq with (eta2 := 
   {{ ((prob (( (x \/ z) <-> k1) /\ ( (y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob (((x \/ z) <-> k1) /\ (z <-> k3)))* (prob (((y \/ z) <-> k2) /\ (z <-> k3)))) }}).
   ------ eapply HConseqLeft with (eta2 := (btoss_pt z ((1/2)%R)  {{ ((prob (( (x \/ z) <-> k1) /\ ( (y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob (((x \/ z) <-> k1) /\ (z <-> k3)))* (prob (((y \/ z) <-> k2) /\ (z <-> k3)))) }})).
     * unfold PAImplies. intros. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. unfold Pteval.
       replace (1-1/2)%R with (1/2)%R by lra. simpl. unfold hf in H. 
       replace     (fun st : state =>
     ((z !-> True; snd st) x \/ (z !-> True; snd st) z <->
      (if k1 then True else False)) /\
     ((z !-> True; snd st) y \/ (z !-> True; snd st) z <->
      (if k2 then True else False)) /\
     ((z !-> True; snd st) z <-> (if k3 then True else False))) 
     with     
     (fun st : state =>
            CBoolexp_of_bexp (BConst k1) st /\
            CBoolexp_of_bexp (BConst k2) st /\
            CBoolexp_of_bexp (BConst k3) st).
     replace (fun st : state =>
     ((z !-> False; snd st) x \/ (z !-> False; snd st) z <->
      (if k1 then True else False)) /\
     ((z !-> False; snd st) y \/ (z !-> False; snd st) z <->
      (if k2 then True else False)) /\
     ((z !-> False; snd st) z <-> (if k3 then True else False))) 
     with (fun st : state =>
            (CBoolexp_of_bexp (BVar x) st <->
             CBoolexp_of_bexp (BConst k1) st) /\
            (CBoolexp_of_bexp (BVar y) st <->
             CBoolexp_of_bexp (BConst k2) st) /\
            ~ CBoolexp_of_bexp (BConst k3) st).
     replace (fun st : state =>
     (z !-> True; snd st) z <-> (if k3 then True else False)) with 
     (fun st : state =>  CBoolexp_of_bexp (BConst k3) st).
     replace (fun st : state =>
     (z !-> False; snd st) z <-> (if k3 then True else False)) with
     (fun st : state =>  ~ CBoolexp_of_bexp (BConst k3) st).
     replace  (1 / 2 * fst ps (fun st : state => CBoolexp_of_bexp (BConst k3) st) +
  1 / 2 * fst ps (fun st : state => ~ CBoolexp_of_bexp (BConst k3) st))%R 
   with ( (1 / 2) * fst ps \{ true \})%R.
   replace (fun st : state =>
     ((z !-> True; snd st) x \/ (z !-> True; snd st) z <->
      (if k1 then True else False)) /\
     ((z !-> True; snd st) z <-> (if k3 then True else False)))
     with (fun st : state =>
            CBoolexp_of_bexp (BConst k1) st /\
            CBoolexp_of_bexp (BConst k3) st).
   replace (fun st : state =>
     ((z !-> False; snd st) x \/ (z !-> False; snd st) z <->
      (if k1 then True else False)) /\
     ((z !-> False; snd st) z <-> (if k3 then True else False)))
     with (fun st : state =>
            (CBoolexp_of_bexp (BVar x) st <->
             CBoolexp_of_bexp (BConst k1) st) /\
            ~ CBoolexp_of_bexp (BConst k3) st).
   replace (fun st : state =>
     ((z !-> True; snd st) y \/ (z !-> True; snd st) z <->
      (if k2 then True else False)) /\
     ((z !-> True; snd st) z <-> (if k3 then True else False)))
     with (fun st : state =>
            CBoolexp_of_bexp (BConst k2) st /\
            CBoolexp_of_bexp (BConst k3) st).
   replace (fun st : state =>
     ((z !-> False; snd st) y \/ (z !-> False; snd st) z <->
      (if k2 then True else False)) /\
     ((z !-> False; snd st) z <-> (if k3 then True else False)))
     with (fun st : state =>
            (CBoolexp_of_bexp (BVar y) st <->
             CBoolexp_of_bexp (BConst k2) st) /\
            ~ CBoolexp_of_bexp (BConst k3) st).
     unfold Pteval in H.
     easy. apply functional_extensionality. intros. apply propositional_extensionality.
     rewrite t_update_eq. tauto. apply functional_extensionality. intros. apply propositional_extensionality.
     rewrite t_update_eq. tauto. apply functional_extensionality. intros. apply propositional_extensionality.
     rewrite t_update_eq. tauto. apply functional_extensionality. intros. apply propositional_extensionality. rewrite t_update_eq. tauto. 
     apply (Rmult_eq_reg_l 2). field_simplify. apply measure_true_dest. easy. apply functional_extensionality. intros. apply propositional_extensionality. rewrite t_update_eq. tauto.
     apply functional_extensionality. intros. apply propositional_extensionality. rewrite t_update_eq. tauto.
     apply functional_extensionality. intros. apply propositional_extensionality. rewrite t_update_eq. tauto.
     apply functional_extensionality. intros. apply propositional_extensionality. rewrite t_update_eq. tauto.
     * apply HBToss.
   ------ eapply HConseqLeft with (eta2 := (basgn_pt a (<{ x \/ z }>) {{ ((prob ((a <-> k1) /\ ( (y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob ((a <-> k1) /\ (z <-> k3)))* (prob (((y \/ z) <-> k2) /\ (z <-> k3)))) }})).
   easy. 
  (* Seq:  b<- y \/ z *)
  eapply HSeq with (eta2 := 
   {{ ((prob ((a <-> k1) /\ ( (y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob ((a <-> k1) /\ (z <-> k3)))* (prob (((y \/ z) <-> k2) /\ (z <-> k3)))) }}).
   ------- apply HBAsgn. 
   ------- eapply HConseqLeft with (eta2 := (basgn_pt b (<{ y \/ z }>) {{ ((prob ((a <-> k1) /\ (b <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))) 
   = ((prob ((a <-> k1) /\ (z <-> k3)))* (prob ((b <-> k2) /\ (z <-> k3)))) }})).
   easy. apply HBAsgn.
Qed.
