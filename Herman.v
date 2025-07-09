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

Module Herman.

Definition a1 : string := "a1".
Definition a2 : string := "a2".
Definition a3 : string := "a3".
Definition y : string := "y".

(* Herman Self Stabilising protocol *)
Definition Herman_guard (a1 a2 a3 : string) : bexp := <{(a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)}>.
Definition Herman : Cmd :=
<{ 
  while (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}>.

Theorem body1 : {{(prob true) = 1 }} <{a1 toss 0.5; a2 toss 0.5; a3 toss 0.5 }> {{(prob true) = 1}}.
Proof. apply HSeq with (eta2 := {{(prob true) = 1}}). 
        + apply HConseqLeft with (eta2 := btoss_pt a1 0.5 ({{(prob true) = 1}})).
          - intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. lra.
          - apply HBToss.
        + apply HSeq with (eta2 := {{(prob true) = 1}}).
          - apply HConseqLeft with (eta2 := btoss_pt a2 0.5 ({{(prob true) = 1}})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. lra. 
            * apply HBToss.
          - apply HConseqLeft with (eta2 := btoss_pt a3 0.5 ({{(prob true) = 1}})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. lra. 
            * apply HBToss.
Qed.

Theorem body2: {{(prob true) = 1 }} <{a1 toss 0.5; a2 toss 0.5; a3 toss 0.5 }> {{(prob (a1 /\ a2 /\ a3)) = (0.125) }}.
Proof. apply HSeq with (eta2 := {{(prob a1) = 0.5}}). 
        + apply HConseqLeft with (eta2 := btoss_pt a1 0.5 ({{(prob a1) = 0.5}})).
          - intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => (a1 !-> True; (snd st)) a1)) with (fst ps {{true}}) by (apply equivalence; intro; easy).
            replace (fst ps (fun st : state => (a1 !-> False; (snd st)) a1)) with (fst ps {{false}}) by (apply equivalence; intro; easy). rewrite empty_set_measure. lra.
          - apply HBToss.
        + apply HSeq with (eta2 := {{(prob (a1 /\ a2)) = 0.25}}).
          - apply HConseqLeft with (eta2 := btoss_pt a2 0.5 ({{(prob (a1 /\ a2)) = 0.25}})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => ((a2 !-> True; (snd st)) a1) /\ ((a2 !-> True; (snd st)) a2))) with (fst ps a1) by (apply equivalence; intro; easy).
              replace (fst ps (fun st : state => ((a2 !-> False; (snd st)) a1) /\ ((a2 !-> False; (snd st)) a2))) with (fst ps {{false}}) by (apply equivalence; easy). rewrite empty_set_measure. lra. 
            * apply HBToss.
          - apply HConseqLeft with (eta2 := btoss_pt a3 0.5 ({{(prob (a1 /\ a2 /\ a3)) = (0.125) }})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => ((a3 !-> True; (snd st)) a1) /\ (((a3 !-> True; (snd st)) a2) /\ ((a3 !-> True; (snd st)) a3)))) with (fst ps (fun st : state => (snd st a1) /\ (snd st a2))) by (apply equivalence; easy).
              replace (fst ps (fun st : state => ((a3 !-> False; (snd st)) a1) /\ (((a3 !-> False; (snd st)) a2) /\ ((a3 !-> False; (snd st)) a3)))) with (fst ps {{false}}) by (apply equivalence; easy). rewrite empty_set_measure. lra. 
            * apply HBToss.
Qed.

Theorem body3: {{(prob true) = 1 }} <{a1 toss 0.5; a2 toss 0.5; a3 toss 0.5 }> {{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }}.
Proof. apply HSeq with (eta2 := {{(prob ~a1) = 0.5}}). 
        + apply HConseqLeft with (eta2 := btoss_pt a1 0.5 ({{(prob ~a1) = 0.5}})).
          - intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => ~((a1 !-> True; (snd st)) a1))) with (fst ps {{false}}) by (apply equivalence; intro; rewrite t_update_eq; easy).
            replace (fst ps (fun st : state => ~((a1 !-> False; (snd st)) a1))) with (fst ps {{true}}) by (apply equivalence; intro; easy). rewrite empty_set_measure. lra.
          - apply HBToss.
        + apply HSeq with (eta2 := {{(prob (~a1 /\ ~a2)) = 0.25}}).
          - apply HConseqLeft with (eta2 := btoss_pt a2 0.5 ({{(prob (~a1 /\ ~a2)) = 0.25}})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => ~((a2 !-> True; (snd st)) a1) /\ ~((a2 !-> True; (snd st)) a2))) with (fst ps {{false}}) by (apply equivalence; intro; rewrite t_update_eq; easy).
              replace (fst ps (fun st : state => ~((a2 !-> False; (snd st)) a1) /\ ~((a2 !-> False; (snd st)) a2))) with (fst ps (fun st : state => ~ (snd st a1))) by (apply equivalence; easy). rewrite empty_set_measure. lra. 
            * apply HBToss.
          - apply HConseqLeft with (eta2 := btoss_pt a3 0.5 ({{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }})).
            * intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. uncoerce_basic. replace (fst ps (fun st : state => ~((a3 !-> True; (snd st)) a1) /\ (~((a3 !-> True; (snd st)) a2) /\ ~((a3 !-> True; (snd st)) a3)))) with (fst ps {{false}}) by (apply equivalence; intro; rewrite t_update_eq; easy).
              replace (fst ps (fun st : state => ~((a3 !-> False; (snd st)) a1) /\ (~((a3 !-> False; (snd st)) a2) /\ ~((a3 !-> False; (snd st)) a3)))) with (fst ps (fun st : state => (~ (snd st a1)) /\ (~ (snd st a2)))) by (apply equivalence; easy). rewrite empty_set_measure. lra. 
            * apply HBToss.
Qed.

Theorem body4: {{(prob true) = 1 }} <{a1 toss 0.5; a2 toss 0.5; a3 toss 0.5 }> {{(prob (~( (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) ))) = 0.75 }}.
Proof. apply HConseqRight with (eta2 := {{(prob true) = 1 /\ (prob (a1 /\ a2 /\ a3)) = (0.125) /\ (prob (~a1 /\ ~a2 /\ ~a3)) = (0.125)}}).
        + intro. uncoerce_basic. rewrite measure_true_dest with (Q := \{(a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) \}).
          rewrite <- fin_additivity. intro. uncoerce_basic H. lra. easy.
        +  apply HAnd. apply body1. apply HAnd. apply body2. apply body3.
Qed. 

Theorem Herman_termination_y_LB: {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) >= y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}
  <{ 
  while (a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3)) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{(prob (true)) >= (1*y)}}.
Proof.
       assert (T: forall (b : bexp) (tempA : Assertion), (b = <{(a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3))}>) -> Assertion_equiv tempA (CBoolexp_of_bexp <{(a1 /\ (a2 /\ a3)) }>) 
          -> {{ ((prob (b /\ tempA)) >= y) /\ ((prob (b /\ tempA)) = (prob true)) }}
<{ 
  while (b) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{ (prob (true)) >=  (1*y) }}).
    * intros. eapply HWhileLB.
      - assert (forall i : nat,
(i < 2) ->
(forall st : state, ((List.nth i (to_list [CBoolexp_of_bexp <{a1 /\ (a2 /\ a3) }>; CBoolexp_of_bexp <{~ a1 /\ (~a2 /\ ~a3) }>]) (fun _ : state => True)) st) -> (Beval b2 st))).
        --  intros i T1 st. destruct i.
            ** simpl. rewrite H. unfold Beval. tauto.
            ** destruct i.
              *** simpl. rewrite H. unfold Beval. tauto.
              *** assert (C : ~ (S (S i)) < 2). lia. contradiction.
        -- apply H1.
      - intros i j T1 T2 st. destruct i.
        -- assert (~ (j < 0)). lia. contradiction.
        -- destruct i.
           ** destruct j. simpl. tauto. assert (~ (S j) < 1). lia. contradiction.
           ** assert (~ (S (S i) < 2)). lia. contradiction.
      - assert (forall i : nat,
(i < 2) ->
((((List.nth i (to_list [0.75%R; 0.75%R]) 0) > 0)%R) \/
 (exists j : nat,
    ((j < i) /\
     (((List.nth j (to_list (List.nth i (to_list [([(1/8)%R; (1/8)%R]); ([(1/8)%R; (1/8)%R])]) (const 0 2))) 0) > 0)%R))))).
        -- intros i T1. left. destruct i. simpl. lra. destruct i. simpl. lra. assert (~ (S (S i)) < 2). lia. contradiction.
        -- exact H1.
      - intros i T1. destruct i.
        -- simpl. unfold int_true_eq_one. unfold inner_conj_geq. unfold apply_func. unfold gamma_geq. unfold gamma_compare. simpl. unfold gamma_geq.
            unfold gamma_compare. rewrite H. apply HAnd. apply HAnd. apply HConseqRight with (eta2 := ({{(prob (a1 /\ a2 /\ a3)) = (0.125) }})). uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. intro. lra.
            apply HConseqLeft with (eta2 := {{(prob true) = 1 }}). intro. unfold Pteval. lra. apply body2.
           apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }}). unfold Pteval. unfold CBoolexp_of_bexp. unfold Beval. intro. lra.
           unfold CBoolexp_of_bexp. unfold Beval. intro. unfold Pteval. uncoerce_basic. lra. apply body3. 
           apply HConseq with (eta2 := ({{(prob true) = 1 }})) (eta3 := ({{(prob (~( (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) ))) = 0.75 }})). intro. uncoerce_basic. lra.
           intro. uncoerce_basic. replace (fst ps (fun st : state => ~(((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3))))))) with (fst ps (fun st : state => (~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3)))))) /\ True)) by (apply equivalence; intro; easy). lra.
           apply body4.
        -- destruct i. 
          ** simpl. unfold int_true_eq_one. unfold inner_conj_geq. unfold apply_func. unfold gamma_geq. unfold gamma_compare. simpl. unfold gamma_geq.
            unfold gamma_compare. rewrite H. apply HAnd. apply HAnd. apply HConseqRight with (eta2 := ({{(prob (a1 /\ a2 /\ a3)) = (0.125) }})). uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. intro. lra.
            apply HConseqLeft with (eta2 := {{(prob true) = 1 }}). intro. unfold Pteval. lra. apply body2.
           apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }}). unfold Pteval. unfold CBoolexp_of_bexp. unfold Beval. intro. lra.
           unfold CBoolexp_of_bexp. unfold Beval. intro. unfold Pteval. uncoerce_basic. lra. apply body3. 
           apply HConseq with (eta2 := ({{(prob true) = 1 }})) (eta3 := ({{(prob (~( (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) ))) = 0.75 }})). intro. uncoerce_basic. lra.
           intro. uncoerce_basic. replace (fst ps (fun st : state => ~(((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3))))))) with (fst ps (fun st : state => (~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3)))))) /\ True)) by (apply equivalence; intro; easy). lra.
           apply body4.
          ** assert (~ (S (S i)) < 2). lia. contradiction.
      - assert (T: forall i : nat,
(i < 2) ->
(lin_ineq_lb i ([1%R; 1%R]) ([([(1 / 8)%R; (1 / 8)%R]); ([(1 / 8)%R; (1 / 8)%R])])
   [0.75%R; 0.75%R])).
        -- intros i T1. destruct i. unfold lin_ineq_lb. simpl. lra. destruct i. unfold lin_ineq_lb. simpl. lra. assert (~ (S (S i)) < 2). lia. contradiction.
        -- apply T.
      - assert (0 < 2). lia. exact H1.
      - intros. simpl. symmetry. apply H0.
      - simpl. lra.
    * assert (H: ({{((prob ((<{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }>)) /\ (<{ (a1 /\ (a2 /\ a3)) }>)) >= y) /\ ((prob ((<{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }>)) /\ (<{ (a1 /\ (a2 /\ a3)) }>)) = (prob (true)))}} 
      while <{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }> do a1 toss 0.5; (a2 toss 0.5; a3 toss 0.5) end
      {{(prob (true)) >= (1 * y)}})). apply T. easy. easy. apply H.
Qed.

Theorem Herman_termination_y_UB: {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) <= y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}
  <{ 
  while (a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3)) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{(prob (true)) <= (1*y)}}.
Proof. 
       assert (T: forall (b : bexp) (tempA : Assertion), (b = <{(a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3))}>) -> Assertion_equiv tempA (CBoolexp_of_bexp <{(a1 /\ (a2 /\ a3)) }>) 
          -> {{ ((prob (b /\ tempA)) <= y) /\ ((prob (b /\ tempA)) = (prob true)) }}
<{ 
  while (b) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{ (prob (true)) <=  (1*y) }}).
    * intros. eapply HWhileUB with (m := 2) (G := [CBoolexp_of_bexp <{a1 /\ (a2 /\ a3) }>; CBoolexp_of_bexp <{~ a1 /\ (~a2 /\ ~a3) }>]) (P := [([(1/8)%R; (1/8)%R]); ([(1/8)%R; (1/8)%R])])
                (T := [0.75%R; 0.75%R]) (X := [1%R; 1%R]) (i := 0).
      - intro. rewrite H. unfold Beval. simpl. tauto.
      - intro. destruct i. 
        ** intro. simpl. unfold int_true_eq_one. unfold inner_conj_leq. unfold PAssertion_conj. unfold zip_gamma_leq. unfold zip_gamma_compare. simpl. unfold gamma_leq.
            unfold gamma_compare. unfold apply_func. apply HAnd.
            -- simpl. apply HAnd.
              ++ apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (a1 /\ a2 /\ a3)) = (0.125) }}). intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. lra.
                  intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra. apply body2.
              ++ apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }}). intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra.
                  intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra. apply body3.
            -- apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~( (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) ))) = 0.75 }}). intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra.
                  intro. unfold CBoolexp_of_bexp. rewrite H. uncoerce_basic.  unfold Beval. uncoerce_basic. replace (fst ps (fun st : state => ~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3))))))) with
                  (fst ps (fun st : state => (~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3)))))) /\ True)) by (apply equivalence; intro; easy). lra. apply body4.
        ** destruct i. intro. simpl. unfold int_true_eq_one. unfold inner_conj_leq. unfold PAssertion_conj. unfold zip_gamma_leq. unfold zip_gamma_compare. simpl. unfold gamma_leq.
            unfold gamma_compare. unfold apply_func. apply HAnd. 
            -- simpl. apply HAnd.
              ++ apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (a1 /\ a2 /\ a3)) = (0.125) }}). intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. lra.
                  intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra. apply body2.
              ++ apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~a1 /\ ~a2 /\ ~a3)) = (0.125) }}). intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra.
                  intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra. apply body3.
            -- apply HConseq with (eta2 := {{(prob true) = 1 }}) (eta3 := {{(prob (~( (a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3) ))) = 0.75 }}). intro. unfold CBoolexp_of_bexp. unfold Beval. uncoerce_basic. lra.
                  intro. unfold CBoolexp_of_bexp. rewrite H. uncoerce_basic.  unfold Beval. uncoerce_basic. replace (fst ps (fun st : state => ~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3))))))) with
                  (fst ps (fun st : state => (~ (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3)))))) /\ True)) by (apply equivalence; intro; easy). lra. apply body4.
            -- assert (~ (S (S i)) < 2). lia. contradiction.
       - intros. destruct i.
          ** unfold lin_ineq. simpl. lra.
          ** destruct i.
              -- unfold lin_ineq. simpl. lra.
              -- assert (~ (S (S i)) < 2). lia. contradiction.
       - lia.
       - simpl. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0. unfold Beval in H0. easy.
       - simpl. lra.
      * assert (H: ({{((prob ((<{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }>)) /\ (<{ (a1 /\ (a2 /\ a3)) }>)) <= y) /\ ((prob ((<{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }>)) /\ (<{ (a1 /\ (a2 /\ a3)) }>)) = (prob (true)))}} 
      while <{ ((a1 /\ (a2 /\ a3)) \/ ((~ a1) /\ ((~ a2) /\ (~ a3)))) }> do a1 toss 0.5; (a2 toss 0.5; a3 toss 0.5) end
      {{(prob (true)) <= (1 * y)}})). apply T. easy. easy. apply H.
Qed. 

Theorem Herman_termination_y : {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}
  <{ 
  while (a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3)) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{(prob (true)) = (1*y)}}.
Proof. apply HConseqRight with (eta2 := {{(prob (true)) <= (1*y) /\ (prob (true)) >= (1*y)}}).
        + intro. unfold Pteval. lra.
        + apply HAnd. apply HConseqLeft with (eta2 := {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) <= y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}).
          * intro. uncoerce_basic. intro. split. lra. lra.
          * apply Herman_termination_y_UB.
          * apply HConseqLeft with (eta2 := {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) >= y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}).
            - intro. uncoerce_basic. intro. split. lra. lra.
            - uncoerce_basic. apply Herman_termination_y_LB.
Qed.

Theorem Herman_temrination : {{(prob (a1 /\ a2 /\ a3)) = 1 /\ (prob (a1 /\ a2 /\ a3)) = (prob true)}}
<{ 
  while (a1 /\ (a2 /\ a3)) \/ (~a1 /\ (~a2 /\ ~a3)) do 
    a1 toss 0.5; 
    a2 toss 0.5;
    a3 toss 0.5 end
}> {{(prob (true)) = (1)}}.
Proof. apply HConseq with (eta2 := eta_update_y_p ({{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}) y 1%R)
                          (eta3 := eta_update_y_p ({{(prob (true)) = (1*y)}}) y 1%R).
        + intro. unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. rewrite t_update_eq. replace (fst ps (fun st : state => (((snd st a1) /\ ((snd st a2) /\ (snd st a3))) \/ ((~ (snd st a1)) /\ ((~ (snd st a2)) /\ (~ (snd st a3))))) /\((snd st a1) /\ ((snd st a2) /\ (snd st a3))))) with (fst ps (fun st : state => (snd st a1) /\ ((snd st a2) /\ (snd st a3)))) by (apply equivalence; intro; tauto). lra.
        + intro. unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. rewrite t_update_eq. lra.
        + apply eliminate_y. 
          - easy.
          - easy.
          - apply HConseqLeft with (eta2 := {{((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = y) /\ ((prob (((a1 /\ a2 /\ a3) \/ (~a1 /\ ~a2 /\ ~a3)) /\ (a1 /\ a2 /\ a3))) = (prob true))}}).
            -- intro. easy.
            -- apply Herman_termination_y.
Qed. 

End Herman.
       
