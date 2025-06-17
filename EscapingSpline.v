Print Libraries.
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

Definition b : string := "b".
Definition val : string := "val".
(* Open Scope com_scope.
Open Scope passertion_scope.
Open Scope hoare_spec_scope. *)

Check Cmd.

Definition example_prog1: Cmd :=
  TAsgn b 1.
Definition half : R := 0.5.

Definition body : Cmd :=
  <{ 
  b toss 0.5;
  if b then val := 2 * val + 1 else val := 2 * val end
}>.

Fixpoint uniform_exp (k : nat) : Cmd :=
  match k with 
    | O => Skip
    | S n => CSeq (uniform_exp n) body
end.

Compute uniform_exp 2.

Theorem body1: forall k : nat, {{(prob (val = k)) = 1 /\ (prob (val = k)) = (prob true)}} body 
                                {{(prob (val = (2 * k))) = 0.5}}.
Proof.
Admitted.

Theorem body2: forall k : nat, {{(prob (val = k)) = 1 /\ (prob (val = k)) = (prob true)}} body 
                                {{(prob (val = (2*k + 1))) = 0.5}}.
Proof.
Admitted.
