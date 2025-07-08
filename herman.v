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

(* Herman Self Stabilising protocol *)
Definition Herman_guard (x1 x2 x3 : string) : bexp := <{(x1 /\ x2 /\ x3) \/ (~x1 /\ ~x2 /\ ~x3)}>.
Definition Herman (x1 x2 x3: string) : Cmd :=
<{ 
  while (x1 /\ x2 /\ x3) \/ (~x1 /\ ~x2 /\ ~x3) do 
    x1 toss 0.5; 
    x2 toss 0.5;
    x3 toss 0.5 end
}>.

Theorem Herman_termination: forall (x1 x2 x3 y : string), (x1 <> x2) /\ (x2 <> x3) /\ (x1 <> y) -> {{((prob (((x1 /\ x2 /\ x3) \/ (~x1 /\ ~x2 /\ ~x3)) /\ (x1 /\ x2 /\ x3))) >= y) /\ ((prob (((x1 /\ x2 /\ x3) \/ (~x1 /\ ~x2 /\ ~x3)) /\ (x1 /\ x2 /\ x3))) = (prob true))}}
  <{ 
  while (x1 /\ (x2 /\ x3)) \/ (~x1 /\ (~x2 /\ ~x3)) do 
    x1 toss 0.5; 
    x2 toss 0.5;
    x3 toss 0.5 end
}> {{(prob (true)) >= (1*y)}}.
Proof. intros x1 x2 x3 y H1.
       assert (T: forall (b : bexp) (tempA : Assertion), (b = <{(x1 /\ (x2 /\ x3)) \/ (~x1 /\ (~x2 /\ ~x3))}>) -> Assertion_equiv tempA (CBoolexp_of_bexp <{(x1 /\ (x2 /\ x3)) }>) 
          -> {{ ((prob (b /\ tempA)) >= y) /\ ((prob (b /\ tempA)) = (prob true)) }}
<{ 
  while (b) do 
    x1 toss 0.5; 
    x2 toss 0.5;
    x3 toss 0.5 end
}> {{ (prob (true)) >=  (1*y) }}).
    * intros. eapply HWhileLB.
      - assert (forall i : nat,
(i < 2) ->
(forall st : state, ((List.nth i (to_list [CBoolexp_of_bexp <{x1 /\ (x2 /\ x3) }>; CBoolexp_of_bexp <{~ x1 /\ (~x2 /\ ~x3) }>]) (fun _ : state => True)) st) -> (Beval b0 st))).
        --  intros i T1 st. destruct i.
            ** simpl. rewrite H. unfold Beval. tauto.
            ** destruct i.
              *** simpl. rewrite H. unfold Beval. tauto.
              *** assert (C : ~ (S (S i)) < 2). lia. contradiction.
        -- apply H2.
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
        -- exact H2.
      - intros i T1. destruct i.
        -- simpl. unfold int_true_eq_one. unfold inner_conj_geq. unfold apply_func. unfold gamma_geq. unfold gamma_compare. simpl. unfold gamma_geq.
            unfold gamma_compare. admit.
        -- destruct i. 
          ** simpl. unfold int_true_eq_one. unfold inner_conj_geq. unfold apply_func. unfold gamma_geq. unfold gamma_compare. simpl. unfold gamma_geq.
            unfold gamma_compare. admit.
          ** assert (~ (S (S i)) < 2). lia. contradiction.
      - assert (T: forall i : nat,
(i < 2) ->
(lin_ineq_lb i ([1%R; 1%R]) ([([(1 / 8)%R; (1 / 8)%R]); ([(1 / 8)%R; (1 / 8)%R])])
   [0.75%R; 0.75%R])).
        -- intros i T1. destruct i. unfold lin_ineq_lb. simpl. lra. destruct i. unfold lin_ineq_lb. simpl. lra. assert (~ (S (S i)) < 2). lia. contradiction.
        -- apply T.
      - assert (0 < 2). lia. exact H2.
      - intros. simpl. symmetry. apply H0.
      - simpl. lra.
    * assert (H: ({{((prob ((<{ ((x1 /\ (x2 /\ x3)) \/ ((~ x1) /\ ((~ x2) /\ (~ x3)))) }>)) /\ (<{ (x1 /\ (x2 /\ x3)) }>)) >= y) /\ ((prob ((<{ ((x1 /\ (x2 /\ x3)) \/ ((~ x1) /\ ((~ x2) /\ (~ x3)))) }>)) /\ (<{ (x1 /\ (x2 /\ x3)) }>)) = (prob (true)))}} 
      while <{ ((x1 /\ (x2 /\ x3)) \/ ((~ x1) /\ ((~ x2) /\ (~ x3)))) }> do x1 toss 0.5; (x2 toss 0.5; x3 toss 0.5) end
      {{(prob (true)) >= (1 * y)}})). apply T. easy. easy. apply H.
Admitted.        
