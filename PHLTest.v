(*Testing out stuff for Probabilistic Hoare Logic project *)

From PHL Require Import Maps.
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
Require Import Classical.

(* Import ListNotations. *)

Module PHL.

(* Defining terms over nat for now
 *)
Inductive Term: Type :=
  | Const (c : nat)
  | Var (x : string)
  | sum (t1 : Term) (t2 : Term)
  | sub (t1 : Term) (t2 : Term)
  | mult (t1 : Term) (t2 : Term).

(* Defining boolean expressions
 *)

Inductive bexp: Type :=
  | BConst (b : bool)
  | BVar (x : string)
  | Leq (t1 : Term) (t2 : Term)
  | Eq (t1 : Term) (t2 : Term)
  | Or (b1 : bexp) (b2 : bexp)
  | Not (b1 : bexp)
  | And (b1 : bexp) (b2 : bexp)
  | Implies (b1 : bexp) (b2 : bexp)
  | Iff (b1 : bexp) (b2 : bexp).

Check total_map nat.

(* Can use record maybe for state
 *)
(*Definition TVal := total_map nat.
Definition BVal := total_map Prop. *)
Definition state := (total_map nat) * (total_map Prop).

(* Evaluating a term in a state *)

Fixpoint Teval (t : Term) (s : state) : nat :=
  match t with
    | Const c => c
    | Var x => (fst s) x
    | sum t1 t2 => (Teval t1 s) + (Teval t2 s)
    | sub t1 t2 => (Teval t1 s) - (Teval t2 s)
    | mult t1 t2 => (Teval t1 s) * (Teval t2 s)
end.

(* Evaluating a bexp in a state
 *)

Fixpoint Beval (b : bexp) (s : state) : Prop :=
  match b with 
    | BConst true => True
    | BConst false => False
    | BVar x => (snd s) x
    | Leq t1 t2 => (Teval t1 s) <= (Teval t2 s)
    | Eq t1 t2 => (Teval t1 s) = (Teval t2 s)
    | Or b1 b2 => (Beval b1 s) \/ (Beval b2 s)
    | Not b1 => ~ (Beval b1 s)
    | And b1 b2 => (Beval b1 s) /\ (Beval b2 s)
    | Implies b1 b2 => (Beval b1 s) -> (Beval b2 s)
    | Iff b1 b2 => (Beval b1 s) <-> (Beval b2 s)
end.


Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.
Open Scope com_scope.

Coercion Const : nat >-> Term.
Coercion Var : string >-> Term.
Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.

(* Terms - built using consts, vars and +/* *)
Notation "x + y"   := (sum x y) (in custom com at level 50, left associativity): com_scope.
Notation "x - y"   := (sub x y) (in custom com at level 50, left associativity): com_scope.
Notation "x * y"   := (mult x y) (in custom com at level 40, left associativity): com_scope.

(* bexps - built using term comparisons and boolean operators *)
Coercion BConst : bool >-> bexp.
Coercion BVar : string >-> bexp.
Definition test: bexp := true.
Notation "'true'"  := (BConst true)  (in custom com at level 0) : com_scope.
Notation "'false'" := (BConst false) (in custom com at level 0) : com_scope.
Notation "x <= y" := (Leq (x:Term) (y:Term)) (in custom com at level 60, left associativity): com_scope.
Notation "x >= y" := (Leq y x) (in custom com at level 60, left associativity): com_scope. 
Notation "x = y" := (Eq y x) (in custom com at level 60, left associativity): com_scope. 
(* If I understand this correctly, level 60 would mean things with level 50/40 would be parsed first, i.e x,y.*)
Notation "'~' x" := (Not x) (in custom com at level 70, left associativity): com_scope.
Notation "x \/ y" := (Or x y) (in custom com at level 80, left associativity): com_scope.
Notation "x /\ y" := (And x y) (in custom com at level 80, left associativity): com_scope.
(* May want to consider changing the level for these *)
Notation "x -> y" := (Implies x y) (in custom com at level 80, left associativity): com_scope.
Notation "x <-> y" := (Iff x y) (in custom com at level 80, left associativity): com_scope.


Definition term_example:Term := (Const 156).
Definition term_shorthand:Term := 156.
Definition term_2: Term := (sum (Const 12)  (Const 13)).
Definition term_2sh: Term := <{ 12 + 13 }>.
Definition bexp_example:bexp :=  Leq (sum (Const 12)  (Const 13)) (Const 156).
Definition  bexp_shorthand:bexp := <{ 12 + 13 <= 14 }>.
Definition term_3:Term->Term := fun x:Term => <{ 12 + x }>.
Definition bexp_3:Term->bexp := fun x => <{ 12 + x <= 12*x }>.



(* com_scope notates how to evaluate various classical formulas/terms given values of variables.
Extending this to states: Recall a classical state is a pair (total_map nat)*(total_map Prop).
Want, to interpret t: Term as  (fun (st: state) => (Teval t st):nat )
*)

Definition Assertion := state -> Prop.

Definition Assertion_equiv (A1 A2 : Assertion) : Prop :=
  forall st: state, A1 st <-> A2 st.

Definition CTermexp: Type :=  state -> nat. (* Classical nat exp.*)
(*Definition CBoolexp: Type := state -> Prop.*) (* Classical  Boolean/Prop exp*)

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P. (* P to 'if state satisfies P'*)
Definition CTermexp_of_nat (n: nat) : CTermexp := fun _=> n. (*  n to 'given state st return n'*)
Definition CTermexp_of_Texp (a: Term): CTermexp := fun st => Teval a st. (* evaluate the term on the state *) 
Definition CBoolexp_of_Prop (P: Prop): Assertion := fun _ => P.
Definition  CBoolexp_of_bexp (b: bexp): Assertion := fun st => Beval b st. (* evaluate the _boolean_ term on the state *)


Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion CTermexp_of_nat : nat >->CTermexp.
Coercion CTermexp_of_Texp : Term >-> CTermexp.
Coercion CBoolexp_of_bexp: bexp >-> Assertion.
Coercion CBoolexp_of_Prop : Sortclass >-> Assertion.


Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope passertion_scope.
Bind Scope passertion_scope with Assertion.
Bind Scope passertion_scope with CTermexp.
Delimit Scope passertion_scope with passertion.
Open Scope passertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : passertion_scope.
Notation "x" := (x%passertion) (in custom assn at level 0, x constr at level 0) : passertion_scope.
Notation "\{ e \}" := e (at level 2, e custom assn at level 99) : passertion_scope.

(* 
Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : passertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : passertion_scope.
Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : passertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : passertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : passertion_scope. *)


(* Handling CBoolexp_of_bexp *)
Notation "'true'" := (fun st => True) (in custom assn at level 65, right associativity) : passertion_scope.
Notation "'false'" := (fun st => False) (in custom assn at level 65, right associativity) : passertion_scope.
Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 70, right associativity) : passertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : passertion_scope.
Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : passertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : passertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : passertion_scope.

Definition assertion_example: Assertion := \{True\}.
Definition assertion_1: Assertion := \{ True -> (False <-> (True /\ True)) \}.

Notation "a + b" := (fun st => ((a:CTermexp) st + (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
Notation "a * b" := (fun st => ((a:CTermexp) st * (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
Notation "a <= b" := (fun st => ((a:CTermexp) st <= (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 
Notation "a >= b" := (fun st => ((b:CTermexp) st <= (a:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 
Notation "a = b" := (fun st => ((b:CTermexp) st = (a:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 

Definition ctermexp_example (a: CTermexp) (b: CTermexp) : CTermexp :=  (fun st => ( (a st) + (b st))%nat).
Definition assertion_2: Assertion := \{ True -> ( (12 + 13) <= 2) \}.
Definition assertion_3: Term -> Assertion  := fun x => \{ x <= 2\}.
Definition assertion_4: bexp -> Assertion  := fun b => \{ b /\ 2 <= 2\}. (* Idk why this works now. *)

(* assertion_sub_term x e P = {set of all states s such that [x := e]s satisfies P}
 *)
Definition assertion_sub_term (x : string) (e : Term) (P : Assertion) : Assertion :=
  fun st => ( P ((x !-> (Teval e st); (fst st)),(snd st))). (* REVIEW if this defn is correct *)

Definition assertion_sub_bexp (x : string) (b : bexp) (P : Assertion) : Assertion :=
  fun st => (P ( (fst st), (x !-> (Beval b st); (snd st))    )).


Notation "P [ X 't->' a ]" := (assertion_sub_term X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : passertion_scope.

Notation "P [ X 'b->' a ]" := (assertion_sub_bexp X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : passertion_scope.


Definition term_sub_example (x:string) (e: Term) (P: Assertion) :Assertion := \{P [x t-> e]\}.
Definition term_sub_1 (x:string) : Assertion := \{ (x <= 2) [x t-> (12+13)]  \}.


Theorem example_eq: forall (x:string) (st:state), \{ (x <= 2) [x t-> (1 + 1)]  \} st <-> \{ 2 <= 2 \} st.
Proof.
intros.
split.
- unfold assertion_sub_term. simpl. intros. easy.
- unfold assertion_sub_term. simpl. intros. unfold t_update. unfold CTermexp_of_nat. rewrite String.eqb_refl. easy.
Qed.



(* Defining a "measure". We are not putting any restrictions such as Measure of two equivalent assertions should be 
equal. *)

Definition Measure : Type := Assertion -> R.

(* Axioms for measures
 *)
Axiom empty_set_measure : forall mu : Measure, mu (fun _ => False) = 0%R.
Axiom equivalence: forall (mu : Measure) (P Q : Assertion), (Assertion_equiv P Q) -> (mu P = mu Q).
Axiom fin_additivity: forall (mu : Measure) (P Q : Assertion), 
    (forall st : state, ~ (P st /\ Q st)) -> ((mu P) + (mu Q))%R = (mu (fun st : state => P st \/ Q st)).
Axiom positive : forall (mu : Measure) (P : Assertion), (mu P >= 0)%R.

Theorem measure_inclusion: forall (mu : Measure) (P Q :Assertion), (forall st : state, P st -> Q st) -> ((mu P) <= (mu Q))%R.
Proof. intros.
        assert (T: (mu Q) = mu (\{(Q /\ ~ P) \/ P\})).
          + apply equivalence. unfold Assertion_equiv. intros. split.
              - tauto.
              - intros. destruct H0. apply H0. apply H. apply H0. 
          + rewrite T.
            assert (T1 : ((mu (\{Q /\ ~ P\})) + (mu (\{ P \})))%R = mu (fun st : state => ((Q st) /\ (~ (P st))) \/ (P st))).
              - apply fin_additivity. intros. tauto.
              - rewrite <- T1.
                assert (T2 : forall (r1 r2 : R), (0 <= r2)%R -> (r1 <= r2 + r1)%R).
                  * intros. lra.
                  * apply T2. apply Rge_le. apply positive.
Qed. 

Theorem measure_true_dest: forall (mu : Measure) (Q : Assertion), (mu \{ true \}) = ((mu (\{Q\})) + (mu \{ ~ Q \}))%R.
Proof.
  intros. replace (mu \{true\}) with (mu (\{ Q \/ ~ Q\})). symmetry. apply fin_additivity. intros. tauto.
  apply equivalence. unfold Assertion_equiv. intros. tauto. 
Qed.

Theorem measure_P_eq_true: forall (mu : Measure) (P : Assertion), ((mu P) = mu (\{ true \}))%R -> ((mu \{ ~ P \}) = 0)%R.
Proof. intros. replace (mu \{true\}) with ((mu (\{P\})) + (mu \{ ~ P \}))%R in H.
        assert (T: forall (r r1 : R), (r1 = r1 + r)%R -> (r = 0)%R). intros. lra. apply T in H. apply H. symmetry. apply measure_true_dest.
Qed.

Theorem measure_inclusion_0: forall (mu : Measure) (P Q: Assertion), (forall st : state, P st -> Q st) -> (mu Q = 0)%R -> (mu P = 0)%R.
Proof. intros mu P Q H1 H2. apply Rle_antisym. assert ((mu P <= mu Q)%R).
       apply measure_inclusion. apply H1. apply Rle_trans with (r2 := mu Q). apply H. right. apply H2. apply Rge_le. apply positive.
Qed.

Theorem measure_AnotB : forall (mu : Measure) (P Q : Assertion), (mu (\{P /\ ~ Q \}) = mu (\{ P \}) - mu (\{ P /\ Q\}))%R.
Proof. intros. replace (mu P) with (mu \{ (P /\ Q) \/ (P /\ ~Q)\}). rewrite <- fin_additivity. lra.
       intros. tauto. apply equivalence. intro. tauto.
Qed.

(* Defining interpretation of rigid variables. *)

Definition Intp := total_map R.

(* Defining probabilistic state
 *)
Definition Pstate := Measure * Intp.

(* Probabilistic state formulas as assertions
 *)


Inductive Pterm : Type :=
  | Preal (r : R)
  | Pvar (x : string)
  | Pint (A : Assertion)
  | Psum (p1 : Pterm) (p2 : Pterm)
  | Pmult (p1 : Pterm) (p2 : Pterm).

(* Function to evaluate Pterms.
 *)

Fixpoint Pteval (t : Pterm) (ps : Pstate): R := 
  match t with
    | Preal r => r
    | Pvar x => (snd ps) x
    | Pint A => (fst ps) A
    | Psum p1 p2 => (Pteval p1 ps) + (Pteval p2 ps)
    | Pmult p1 p2 => (Pteval p1 ps) * (Pteval p2 ps)
end.



Definition PAssertion : Type := Pstate -> Prop.


(* PAssertion Notation. TODO: Scoping *)

Definition PTermexp: Type :=  Pstate -> R.
(*Definition CBoolexp: Type := state -> Prop.*) (* Classical  Boolean/Prop exp*)

Definition Passert_of_Prop (P : Prop) : PAssertion := fun _ => P.
Definition PTerm_of_R (r: R) : PTermexp := fun _=> r. 
Definition PTermexp_of_pterm (p: Pterm): PTermexp := fun ps => Pteval p ps. (* evaluate the term on the state *) 


Coercion Passert_of_Prop : Sortclass >-> PAssertion.
Coercion PTerm_of_R : R >->PTermexp.
Coercion PTermexp_of_pterm: Pterm >-> PTermexp.

Declare Custom Entry passn. (* The grammar for Hoare logic Assertions *)
(*Declare Scope passertion_scope.*)
Bind Scope passertion_scope with PAssertion.
Bind Scope passertion_scope with PTermexp.
Delimit Scope passertion_scope with passertion.
Open Scope passertion_scope.


Coercion Preal : R >-> Pterm.
Coercion Pvar : string >-> Pterm.
Coercion Pint : Assertion >-> Pterm. (* ??? *)
Notation "( x )" := x (in custom passn at level 0, x at level 99) : passertion_scope.
Notation "x" := (x%passertion) (in custom passn at level 0, x constr at level 0) : passertion_scope.
Notation "{{ e }}" := e (at level 2, e custom passn at level 99) : passertion_scope.


Notation "'true'" := (fun st => True) (in custom passn at level 65, right associativity) : passertion_scope.
Notation "'false'" := (fun st => False) (in custom passn at level 65, right associativity) : passertion_scope.
Notation "P -> Q" := (fun st => (P:PAssertion) st -> (Q:PAssertion) st) (in custom passn at level 70, right associativity) : passertion_scope.
Notation "P <-> Q" := (fun st => (P:PAssertion) st <-> (Q:PAssertion) st) (in custom passn at level 95) : passertion_scope.
Notation "P \/ Q" := (fun st => (P:PAssertion) st \/ (Q:PAssertion) st) (in custom passn at level 85, right associativity) : passertion_scope.
Notation "P /\ Q" := (fun st => (P:PAssertion) st /\ (Q:PAssertion) st) (in custom passn at level 80, right associativity) : passertion_scope.
Notation "~ P" := (fun st => ~ ((P:PAssertion) st)) (in custom passn at level 75, right associativity) : passertion_scope.

Definition passertion_example: PAssertion := {{true}}.
Definition passertion_1: PAssertion := {{ true -> (false <-> (true /\ true)) }}.

Notation "a + b" := (fun st => ((a:PTermexp) st + (b:PTermexp) st)%R) (in custom passn at level 50, left associativity) : passertion_scope.
Notation "a * b" := (fun st => ((a:PTermexp) st * (b:PTermexp) st)%R) (in custom passn at level 50, left associativity) : passertion_scope.
Notation "'prob' a" := (fun st => (Pteval (Pint a) st)) (in custom passn at level 40, a custom assn at level 99, left associativity) : passertion_scope.
Notation "a <= b" := (fun st => ((a:PTermexp) st <= (b:PTermexp) st)%R) (in custom passn at level 50, left associativity) : passertion_scope. 
Notation "a >= b" := (fun st => ((b:PTermexp) st <= (a:PTermexp) st)%R) (in custom passn at level 50, left associativity) : passertion_scope. 
Notation "a = b" := (fun st => ((a:PTermexp) st = (b:PTermexp) st)%R) (in custom passn at level 50, left associativity) : passertion_scope. 


Definition ptermexp_example (a: PTermexp) (b: PTermexp) : PTermexp :=  (fun st => ( (a st) + (b st))%R).
Definition passertion_2: PAssertion := {{ true -> ( (12 + 13) <= 2) }}.
Definition passertion_3: Pterm -> PAssertion  := fun x => {{ x <= 2}}.
Check fun (x:Pterm) => {{ x <= 2}}.
Check {{(prob true) = 1}}.

(* ----------------------------------------------
  Defining stuff needed for assignment rules
 *)

(* measure_sub_term x e mu = [x : = e] mu i.e. the measure obtained after transforming mu by x : = e
 *)
Definition measure_sub_term (x : string) (e : Term) (mu : Measure) : Measure :=
  fun (A : Assertion) => 
    (mu (assertion_sub_term x e A)).

(* tasgn_pt x e eta = {set of all measures mu such that [x : = e]mu \models eta}
     tasgn rule : {tasgn_pt x e eta}[x := e]{eta}
 *)
Definition tasgn_pt (x : string) (e : Term) (eta : PAssertion) : PAssertion :=
  fun ps => 
     eta ((measure_sub_term x e (fst ps)), snd ps).

(* measure_sub_bexp x b mu = [x : = b] mu i.e. the measure obtained after transforming mu by x : = e
 *)
Definition measure_sub_bexp (x : string) (b : bexp) (mu : Measure) : Measure :=
  fun (A : Assertion) => 
    (mu (assertion_sub_bexp x b A)).

(* basgn_pt x b eta = {set of all measures mu such that [x : = b]mu \models eta}
    basgn rule : {basgn_pt x b eta}[x := b]{eta}
 *)
Definition basgn_pt (x : string) (b : bexp) (eta : PAssertion) : PAssertion :=
  fun ps => 
     (eta (measure_sub_bexp x b (fst ps), snd ps)).


Notation "P [[ X 't->' a ]]" := (tasgn_pt X a P)
                              (in custom passn at level 10, left associativity, P custom passn, X global, a custom com) : passertion_scope.

Notation "P [[ X 'b->' a ]]" := (basgn_pt X a P)
                              (in custom passn at level 10, left associativity, P custom passn, X global, a custom com) : passertion_scope.


Definition pterm_sub_example (x:string) (e: Term) (P: PAssertion) : PAssertion := {{P [[x t-> e]]}}.
Definition pterm_sub_1 (x:string) : PAssertion := {{ (x <= 2) [[x t-> (12+13)]]  }}.
Definition passert_1 (x:string) :  PAssertion := {{ (prob (x = 1)) <= 1 }}.

(* -------------------------------------------------------
 *)
(* Example of PAssertion
 *)

Definition probability_measures_long : PAssertion :=       (* All measures that have total measure 1 *)
  fun ps => ((fst ps) (fun st => True)) = 1%R.


Definition probability_measures : PAssertion :=
    {{ (prob true) = 1 }}.

(* --------------------------------------------------------
  Defining stuff for toss rule
 *)
(* measure_sub_toss x r mu = [toss(x,r)]mu  CANNOT SEEM TO USE * AND + HERE
 *)

Definition measure_sub_btoss (x : string) (r : R) (mu : Measure) : Measure :=
  fun P =>( (r * ((measure_sub_bexp x <{true}> mu) P))%R + ((1 - r)%R * ((measure_sub_bexp x <{false}> mu) P))%R )%R.

(* btoss_pt x r eta = {set of all measures mu such that [toss(x,r)]mu \models eta
 *)
Definition btoss_pt (x : string) (r : R) (eta: PAssertion) : PAssertion :=
  fun ps =>
    (eta (measure_sub_btoss x r (fst ps), snd ps)).

(* --------------------------------------------------------
 *)


(* --------------------------------------------------------
  Defining stuff for cons rule
 *)
(* PAssertion implications
 *)
Definition PAImplies (eta1 : PAssertion) (eta2 : PAssertion) : Prop :=
  forall ps, eta1 ps -> eta2 ps.


(* --------------------------------------------------------
  Defining stuff for if-then-else rule
 *)
(* Given measure mu and guard B, Measure_cond_B mu B = mu/B
 *)
Definition Measure_cond_B (mu : Measure) (B : bexp) : Measure :=
  fun P : Assertion => mu (fun st => (P st) /\ (Beval B st)).

(* Given psf eta and guard B, PAcondB eta B = eta/B
 *)
Definition PAcondB (eta : PAssertion) (B : bexp) : PAssertion :=
  fun ps => eta (Measure_cond_B (fst ps) B, snd ps).

(* Defining eta1 /\_B eta2 required in if-then-else rule
 *)

Definition psfBpsf (eta1 : PAssertion) (eta2 : PAssertion) (B : bexp) : PAssertion :=
  fun ps => (PAcondB eta1 B ps) /\ (PAcondB eta2 (Not B) ps).

Notation " P / B " := (PAcondB P B)
        (in custom passn at level 96, left associativity, P custom passn, B custom assn) : passertion_scope.
Notation " P / B \ Q" := (psfBpsf P Q B)
        (in custom passn at level 96, left associativity, P custom passn, Q custom passn, B custom assn) : passertion_scope.


(* --------------------------------------------------------
  Defining stuff for ELIMV rule
 *)

(* Updating probabilistic state (mu, rho) to (mu, rho[y -> r])
 *)
Definition pstate_update (ps : Pstate) (y : string) (r : R) : Pstate :=
  (fst ps, (y !-> r;(snd ps))). 

(* value of pterm p is invariant to changes in interpretation of y
 *)
Definition p_inv_y (p : Pterm) (y : string) : Prop :=
  forall (ps : Pstate) (r1 r2 : R), (Pteval p (pstate_update ps y r1)) = (Pteval p (pstate_update ps y r2)).

(* set of pstates satisfying eta is invariant to changes in interpretation of y   *)
Definition eta_inv_y (eta : PAssertion) (y : string) : Prop :=
  forall (ps : Pstate) (r1 r2 : R), eta (pstate_update ps y r1) <-> eta (pstate_update ps y r2).

(* Defining eta^y_p used in ELIMV rule
 *)
Definition eta_update_y_p (eta : PAssertion) (y : string) (p : Pterm) : PAssertion :=
  fun (ps : Pstate) => eta (pstate_update ps y (Pteval p ps)).

(* ----------------------------------------------------------
 *)
(* Syntax of programming language *)
Inductive Cmd : Type :=
  | Skip 
  | TAsgn (x : string) (e : Term)
  | BAsgn (x : string) (e : bexp)
  | BToss (x : string) (r : R)
  | CSeq (c1 : Cmd) (c2 : Cmd)
  | IfThen (g : bexp) (c1 : Cmd) (c2 : Cmd)
  | While (g : bexp) (c1 : Cmd).

Notation "'skip'"  :=
         Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (TAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x b= y " := 
         (BAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation " x 'toss' r " :=
          (BToss x r)
              (in custom com at level 0, x constr at level 0,
             r constr at level 0, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (IfThen x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (While x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Definition example_prog1: Cmd :=
  <{
      "X" := 1;
      "Y" := 2;
      if true then "X" := 2 else "Y" := 1 end
      }>.

Print example_prog1.

Definition is_analytical (P : PAssertion) := forall ps1 ps2: Pstate, 
  snd ps1 = snd ps2 -> (P ps1 <-> P ps2).

Definition is_analytical_pterm (t : Pterm) := forall ps1 ps2: Pstate, 
  snd ps1 = snd ps2 -> Pteval t ps1 = Pteval t ps2.

(* -----------------Functions to define While rule ------------------------------ *)

Fixpoint vector_to_conj (n : nat) (G : Vector.t Assertion n) : Assertion :=
  match G with
  | nil _ => (fun st : state => True)
  | cons _ A n tl => (fun st : state => (A st) /\ (vector_to_conj _ tl) st) 
end.

Fixpoint vector_to_disj (n : nat) (G : Vector.t Assertion n) : Assertion :=
  match G with
  | nil _ => (fun st : state => False)
  | cons _ A n tl => (fun st : state => (A st) \/ (vector_to_disj _ tl) st) 
end.


(* Fixpoint list_to_disj (G : list Assertion) : Assertion :=
  match G with
  | nil => (fun st : state => False)
  | hd :: tl => (fun (st : state) => hd st \/ (list_to_disj tl) st)
end.

Fixpoint inner_conj (gamma : Assertion) (P : list R) : PAssertion :=
  match P with
  | nil => (fun ps => True)
  | hd :: tl => (fun ps => (Rle (Pteval (Pint gamma) ps) hd) /\ ((inner_conj gamma tl) ps))
end. *)

Definition int_true_eq_one (gamma : Assertion) : PAssertion := {{ ((prob gamma) = 1) /\ ((prob gamma) = (prob true)) }}.

Definition int_true_leq_R (gamma: Assertion) (r: R): PAssertion := {{ ((prob gamma) <= r) /\ ((prob gamma) = (prob true)) }}.

Fixpoint convert_A_to_PA (m : nat) (G : Vector.t Assertion m) : (Vector.t PAssertion m) :=
  match G with 
  | (nil _) => (nil _)
  | (cons _ _ _ tl) => cons _ (fun ps => True) _ (convert_A_to_PA _ tl)
end.

Definition head_vector (T : Type) (m : nat) (G : Vector.t T m) :=
  match G in (Vector.t _ n) return (match n with
                                      | O => unit
                                      | S _ => T end) with
  | (nil _) => tt
  | (cons _ hd _ tl) => hd
end.

Definition tail_vector (T : Type) (m : nat) (G : Vector.t T m) :=
  match G in (Vector.t _ n) return (match n with O => unit | S n' => Vector.t T n' end) with
  | (nil _) => tt
  | (cons _ hd _ tl) => tl
end.

(* [asserts] [R] ---> [pterm <= R] (passert) *)


Fixpoint zip {A B C: Type} {n : nat} (f: A->B-> C) (a : Vector.t A n) (b : Vector.t B n) : Vector.t C n :=
match a in Vector.t _ n return Vector.t B n -> Vector.t C n  with
| ha :: ta => fun b => (f ha (Vector.hd b)) :: zip f ta (Vector.tl b)
| [] => fun _ => []
end b.


Definition zip_sum {n:nat} (a: Vector.t nat n) (b: Vector.t nat n) : (Vector.t nat n) :=
  zip add a b
.


Definition zip_gamma_compare {n: nat} (op: Assertion -> R -> PAssertion)(gammas: Vector.t Assertion n) (rs: Vector.t R n) : Vector.t PAssertion n :=
  zip (fun (g: Assertion) (r: R) =>  op g r) 
    gammas rs .

Definition gamma_compare (op: R -> R -> Prop) (gamma: Assertion) (r: R) : PAssertion :=
    (  fun (st: Pstate) => (op (( PTermexp_of_pterm (Pint gamma)) st) ((PTerm_of_R r) st))  ).


Definition gamma_leq := gamma_compare Rle.
Definition gamma_eq := gamma_compare (@eq R).
Definition gamma_geq := gamma_compare Rge.
Definition zip_gamma_leq {n: nat} (gammas: Vector.t Assertion n) (rs: Vector.t R n) : Vector.t PAssertion n :=
  zip_gamma_compare gamma_leq gammas rs.
Definition zip_gamma_geq {n: nat} (gammas: Vector.t Assertion n) (rs: Vector.t R n) : Vector.t PAssertion n :=
  zip_gamma_compare gamma_geq gammas rs.
Definition zip_gamma_eq {n: nat} (gammas: Vector.t Assertion n) (rs: Vector.t R n) : Vector.t PAssertion n :=
  zip_gamma_compare gamma_eq gammas rs.



Fixpoint PAssertion_conj {n: nat} (vec: Vector.t PAssertion n) : PAssertion := 
  match vec with
  | [] => (fun ps => True)
  | hd:: tl => (fun ps => (hd ps) /\ ((PAssertion_conj tl) ps))
end.

Definition inner_conj_leq {n: nat} (gammas: Vector.t Assertion n) (rs: Vector.t R n) : PAssertion :=
  PAssertion_conj (zip_gamma_leq gammas rs).

Definition inner_conj_geq {n: nat} (gammas: Vector.t Assertion n) (rs: Vector.t R n) : PAssertion :=
  PAssertion_conj (zip_gamma_geq gammas rs).


(*Definition antecedent_leq {n: nat} (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n) : Vector.t PAssertion n :=
     fun (argVecR: Vector.t R n) (argR: R) => (fun ps => ((inner_conj_leq gammas (Vector.nth r2 i)) ps) /\ ((gamma_leq (\{ (~beta) /\ gamma \}) (Vector.nth r1 i) ) ps)). 
*)

Definition apply_func {A B: Type} (f: A->B) (x: A) := f x.


Fixpoint vector_sum {n: nat} (X: Vector.t R n) : R :=
  match X with
  | [] => 0%R
  | hd:: tl => (hd + vector_sum tl)%R 
end.


Definition lin_ineq {n: nat} (i: nat) (X: Vector.t R n) (r2: Vector.t (Vector.t R n) n) (r1: Vector.t R n) : Prop :=
     Rge (List.nth i (Vector.to_list X) 0%R)  ((vector_sum (zip Rmult (List.nth i (Vector.to_list r2) (const 0%R n)) (X))) + (List.nth i (Vector.to_list r1) (0%R)))%R. 

Definition lin_ineq_lb {n: nat} (i: nat) (X: Vector.t R n) (r2: Vector.t (Vector.t R n) n) (r1: Vector.t R n) : Prop :=
     Rle (List.nth i (Vector.to_list X) 0%R)  ((vector_sum (zip Rmult (List.nth i (Vector.to_list r2) (const 0%R n)) (X))) + (List.nth i (Vector.to_list r1) (0%R)))%R.

(*
Fixpoint inner_ineqs (m : nat) (G : Vector.t Assertion m) (P : Vector.t R m) : (Vector.t PAssertion m) :=
  match m with
  | O => (nil _)
  | S n => cons _ (Rle (Pteval (Pint (head_vector Assertion (S n) G)) (head_vector R m P))) _ (inner_ineqs (tail_vector Assertion m G) (tail_vector R m P))
end.

Fixpoint inner_conj (m : nat) (gamma : Assertion) (P : Vector.t R m) : PAssertion :=
  match P with
  | nil _ => (fun ps => True)
  | cons _ r m tl => (fun ps => (Rle (Pteval (Pint gamma) ps) r) /\ (inner_conj _ gamma tl) ps)
end.
Definition post_wh (m : nat) (beta gamma: Assertion) (P : Vector.t R m) (T : Vector.t R m) : PAssertion :=
  fun ps => (inner_conj m gamma P) ps /\ (Rle (Pteval (Pint (~ beta /\ gamma))) ) *)


Fixpoint rev_map {n: nat} {A B: Type} (f_vec: Vector.t (A->B) n) (a: A) :  Vector.t B n :=
  match f_vec with
    | [] => []
    | hd :: tl => (hd a) :: (rev_map tl a)
 end.

(* Returns a vector of PAssertions V where V[i] = /\_{j} gamma_ij <=q r_ij /\ ~beta /\ gamma <= r_i *)
Definition antecedent_leq {n: nat} (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n) : Vector.t PAssertion n :=
     zip apply_func 
        (Vector.map 
            (fun (argR: R) => 
                  fun (argVecR: Vector.t R n)  => 
                      (fun ps => ((inner_conj_leq gammas argVecR) ps) /\ ((gamma_leq (\{ (~beta) /\ gamma \}) argR ) ps)))
          r1)
        r2. 

Definition antleq2 {n: nat} (i: nat) (gammas: Vector.t Assertion n) (r2: Vector.t R n) (beta gamma: Assertion) (r1: R) : PAssertion :=
           fun ps =>( ((inner_conj_leq gammas r2) ps)  /\    ((gamma_leq (\{ (~beta) /\ gamma \}) r1) ps) ).

Definition antgeq2 {n: nat} (i: nat) (gammas: Vector.t Assertion n) (r2: Vector.t R n) (beta gamma: Assertion) (r1: R) : PAssertion :=
           fun ps =>( ((inner_conj_geq gammas r2) ps)  /\    ((gamma_geq (\{ (~beta) /\ gamma \}) r1) ps) ).




Definition antecedent_geq {n: nat} (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n) : Vector.t PAssertion n :=
     zip apply_func 
        (Vector.map 
            (fun (argR: R) => 
                  fun (argVecR: Vector.t R n)  => 
                      (fun ps => ((inner_conj_geq gammas argVecR) ps) /\ ((gamma_geq (\{ (~beta) /\ gamma \}) argR ) ps)))
          r1)
        r2. 

(* Input - vector of preconditions P, a command c, vector of postconiditions Q, Returns - vector of hoare P c Q *)
Definition hoare_list {n: nat} (hoare: PAssertion -> Cmd -> PAssertion -> Prop) 
      (P: Vector.t PAssertion n) (c: Cmd) (Q: Vector.t PAssertion n) : Vector.t Prop n :=
       zip apply_func (rev_map (Vector.map hoare P) c) Q. 

Check Vector.fold_right.
Check Vector.fold_left.

Definition hoare_list_leq (hoare:  PAssertion -> Cmd -> PAssertion -> Prop) (s: Cmd)  
 (n: nat) (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n): Prop  := 
  Vector.fold_right and  (hoare_list hoare (Vector.map int_true_eq_one gammas) s (antecedent_leq gammas r2 beta gamma  r1)) True.  

(*Fixpoint vec_to_func {n: nat} {A: Type} (def: Type)  (vec: Vector.t A n) : nary_type n A :=
  match vec with
  | [] => 
  | hd:: tl => hd->(vec_to_func def tl)
end.*)
Check hoare_list_leq.
Check Vector.nth.
Inductive dummy : PAssertion -> Cmd -> PAssertion -> Prop :=
  | all: forall P s Q, dummy P s Q. 

Check hoare_list_leq (fun P s Q => dummy P s Q).
(*

m : nat

f0->f1->f2->...->fm

*)


Fixpoint nary_type (n: nat) (A: Type) : Type :=
match n with 
| 0 => A
| S n' => A -> nary_type n' A
end.

Theorem fdafd : nary_type 0 Prop = Prop.
Proof.
simpl. auto.
Qed.



Fixpoint vec_to_func {n: nat} (def: Prop) (vec: Vector.t Prop n) : Type :=
  match vec with
  | [] => def
  | hd:: tl => hd->(vec_to_func def tl)
end.

(* 
Definition arrow {hoare:  PAssertion -> Cmd -> PAssertion -> Prop} {s: Cmd}  
 {n: nat} (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n): Prop  := 
  vec_to_func True  (hoare_list hoare (Vector.map int_true_eq_one gammas) s (antecedent_leq gammas r2 beta gamma  r1)).  

*)

(* Helper functions for While lower bound rule *)


(* Hoare triples
 *)
Inductive hoare_triple : PAssertion -> Cmd -> PAssertion -> Prop :=
  | HSkip :
    forall (eta : PAssertion) (c : Cmd), hoare_triple eta c eta
  | HTAsgn : 
     forall (eta: PAssertion) (x : string) (e : Term), hoare_triple (tasgn_pt x e eta) (TAsgn x e) eta
  | HBAsgn : 
    forall (eta: PAssertion) (x : string) (b : bexp), hoare_triple (basgn_pt x b eta) (BAsgn x b) eta
  | HBToss :
    forall (eta: PAssertion) (x : string) (r : R), hoare_triple (btoss_pt x r eta) (BToss x r) eta
  | HConseq : 
    forall (eta1 : PAssertion) (eta2 : PAssertion) (eta3 : PAssertion) (eta4 : PAssertion) (c : Cmd), 
      PAImplies eta1 eta2 -> PAImplies eta3 eta4 -> hoare_triple eta2 c eta3 -> hoare_triple eta1 c eta4
  | HIfThen : 
    forall (eta1 eta2 : PAssertion) (Q : Assertion) (y1 y2 : string) (c1 c2 : Cmd) (g : bexp),
      hoare_triple eta1 c1 (fun ps => ((snd ps) y1) = ((fst ps) Q)) -> hoare_triple eta2 c2 (fun ps => ((snd ps) y2) = ((fst ps) Q))
      -> hoare_triple (psfBpsf eta1 eta2 g) (IfThen g c1 c2) (fun ps => (Rplus ((snd ps) y1) ((snd ps) y2)) = ((fst ps) Q))
  | HElimv :
    forall (eta1 eta2 : PAssertion) (y : string) (p : Pterm) (c : Cmd), hoare_triple (fun ps => eta1 ps /\ ((snd ps) y) = (Pteval p ps)) c eta2 ->
      p_inv_y p y -> eta_inv_y eta2 y -> hoare_triple (eta_update_y_p eta1 y p) c eta2
  | HSeq :
    forall (eta1 eta2 eta3 : PAssertion) (c1 c2 : Cmd), hoare_triple eta1 c1 eta2 -> hoare_triple eta2 c2 eta3 -> hoare_triple eta1 (CSeq c1 c2) eta3

  | HFree : forall (eta : PAssertion) (c : Cmd), is_analytical eta -> hoare_triple eta c eta

  | HAnd : forall (eta0 eta1 eta2 : PAssertion) (c : Cmd), hoare_triple eta0 c eta1 -> hoare_triple eta0 c eta2 -> hoare_triple eta0 c {{eta1 /\ eta2}}
  
  | HOr : forall (eta0 eta1 eta2 : PAssertion) (c : Cmd), hoare_triple eta0 c eta2 -> hoare_triple eta1 c eta2 -> hoare_triple {{eta0 \/ eta1}} c eta2
  
  | HWhileUB : forall (m : nat) (beta : bexp) (gamma: Assertion) (s : Cmd) (G : Vector.t Assertion m) (X : Vector.t R m) (P : Vector.t (Vector.t R m) m) (T : Vector.t R m),
      (forall st, Beval beta st -> (vector_to_disj m G) st) -> 

             (* (forall (i: Fin.t m), 
                    hoare_triple (Vector.nth (Vector.map int_true_eq_one G) i) s (Vector.nth (antecedent_leq G P beta gamma  T) i)
              ) *)
              (forall i : nat, (i < m) -> 
                    (hoare_triple (List.nth i (Vector.to_list (Vector.map int_true_eq_one G)) {{true}}) s (List.nth i (Vector.to_list (antecedent_leq G P beta gamma T)) {{true}}))
              )
            (* (hoare_list_leq (fun (P : PAssertion) (s : Cmd) (Q : PAssertion) => hoare_triple P s Q) s m G P (CBoolexp_of_bexp beta) gamma T)  
      (list_of_triples -> Prop) *)
           (* vec_to_func True  (hoare_list hoare_triple (Vector.map int_true_eq_one G) s (antecedent_leq G P beta gamma  T))  *)

          (* @hoare_list_leq hoare_triple s m G P beta gamma T *)

      -> (forall (i:nat), (i < m) -> lin_ineq i X P T)
      -> (forall (i: nat) (y: string) (tempAssertion : Assertion) (tempR : R), 
              (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st <-> tempAssertion st) ->
              ((List.nth i (Vector.to_list X) 0%R) = tempR) ->
              hoare_triple {{((prob (beta /\ tempAssertion)) <= y) /\ ((prob (beta /\ tempAssertion)) = (prob true)) }}
                            <{ while beta do s end }>
                            {{(prob gamma) <= (tempR*y) }}
              (* hoare_triple (fun ps =>  (int_true_leq_R 
                        (fun st => (Beval beta st) /\ (tempAssertion st)) 
                    ((snd ps) y)) ps) <{ while beta do s end }> (fun ps => ( gamma_leq gamma (Rmult tempR ((snd ps) y))) ps) *)
          )
  | HWhileLB : forall (m : nat) (beta : bexp) (gamma: Assertion) (s : Cmd) (G : Vector.t Assertion m) (X : Vector.t R m) (P : Vector.t (Vector.t R m) m) (T : Vector.t R m),
              (forall (i : nat), (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st -> Beval beta st))
                -> (forall (i j : nat), (i < m) -> (j < i) -> (forall st, ~ (((List.nth i (Vector.to_list G) {{true}}) st) /\ ((List.nth j (Vector.to_list G) {{true}}) st))))
                -> (forall (i : nat), (i < m) -> ((List.nth i (Vector.to_list T) 0%R) > 0)%R \/ exists (j : nat), (j < i) /\ ((List.nth j (Vector.to_list (List.nth i (Vector.to_list P) (const 0%R m))) 0%R) > 0)%R)
                -> (forall i : nat, (i < m) -> 
                    (hoare_triple (List.nth i (Vector.to_list (Vector.map int_true_eq_one G)) {{true}}) s (List.nth i (Vector.to_list (antecedent_geq G P beta gamma T)) {{true}}))
              )
                -> (forall (i:nat), (i < m) -> lin_ineq_lb i X P T)
                -> (forall (i: nat) (y: string) (tempAssertion : Assertion) (tempR : R), 
              (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st <-> tempAssertion st) ->
              ((List.nth i (Vector.to_list X) 0%R) = tempR) ->
              hoare_triple {{((prob (beta /\ tempAssertion)) >= y) /\ ((prob (beta /\ tempAssertion)) = (prob true)) }}
                            <{ while beta do s end }>
                            {{(prob gamma) >= (tempR*y) }}
              (* hoare_triple (fun ps =>  (int_true_leq_R 
                        (fun st => (Beval beta st) /\ (tempAssertion st)) 
                    ((snd ps) y)) ps) <{ while beta do s end }> (fun ps => ( gamma_leq gamma (Rmult tempR ((snd ps) y))) ps) *)
          )

   | HWhileLB2 : forall (m : nat) (beta : bexp) (gamma: Assertion) (s : Cmd) (G : Vector.t Assertion m) (X : Vector.t R m) (P : Vector.t (Vector.t R m) m) (T : Vector.t R m),
              (forall (i : nat), (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st -> Beval beta st))
                -> (forall (i j : nat), (i < m) -> (j < i) -> (forall st, ~ (((List.nth i (Vector.to_list G) {{true}}) st) /\ ((List.nth j (Vector.to_list G) {{true}}) st))))
                -> (forall (i : nat), (i < m) -> ((List.nth i (Vector.to_list T) 0%R) > 0)%R \/ exists (j : nat), (j < i) /\ ((List.nth j (Vector.to_list (List.nth i (Vector.to_list P) (const 0%R m))) 0%R) > 0)%R)
                -> (forall i : nat, (i < m) -> 
                      (hoare_triple (List.nth i (Vector.to_list (Vector.map int_true_eq_one G)) {{true}}) 
                                          s 
                       (antgeq2 i G (List.nth i (Vector.to_list P) (const 0%R m)) beta gamma (List.nth i (Vector.to_list T) (0%R)) ))
              )
                -> (forall (i:nat), (i < m) -> lin_ineq_lb i X P T)
                -> (forall (i: nat) (y: string) (tempAssertion : Assertion) (tempR : R), 
              (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st <-> tempAssertion st) ->
              ((List.nth i (Vector.to_list X) 0%R) = tempR) ->
              hoare_triple {{((prob (beta /\ tempAssertion)) >= y) /\ ((prob (beta /\ tempAssertion)) = (prob true)) }}
                            <{ while beta do s end }>
                            {{(prob gamma) >= (tempR*y) }}
              (* hoare_triple (fun ps =>  (int_true_leq_R 
                        (fun st => (Beval beta st) /\ (tempAssertion st)) 
                    ((snd ps) y)) ps) <{ while beta do s end }> (fun ps => ( gamma_leq gamma (Rmult tempR ((snd ps) y))) ps) *)
          )

. 
(* m = (S^m 0) *)

 


(* fi => hoare_triple i
While b do s od
{P} s {Q}
[hoare_triple 1, hoare_triple 2,... hoare_triple m] <= [ f1, f2, ...., fm] *)
(* {0, 1,...m} *)

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P ->> Q" := (PAImplies P Q) 
        (in custom passn at level 96, left associativity, P custom passn, Q custom passn) : hoare_spec_scope.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q)
    (at level 2, P custom passn at level 99, c custom com at level 99, Q custom passn at level 99)
    : hoare_spec_scope.

Definition triple1 : Prop := {{ (prob true) = 1 }} "x" := 1 {{ (prob true) = 1}}.
(* Proof attempts
 *)
(* {int (true) = 1} [x := 1] {int (x = 1) = 1}
 *)

Check fun x:string => {{ ((prob (x = 1)) = 1) [[ x t-> 1]]}}.

(*

Theorem proof_aux: forall x: string, {{ ((prob (x = 1)) = 1) [[ x t-> 1]]}} = {{(prob true) = 1}}.
Proof.

  unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl.






Definition assertion_sub_term (x : string) (e : Term) (P : Assertion) : Assertion :=
  fun st => ( P ((x !-> (Teval e st); (fst st)),(snd st))). (* REVIEW if this defn is correct *)

Definition assertion_sub_bexp (x : string) (b : bexp) (P : Assertion) : Assertion :=
  fun st => (P ( (fst st), (x !-> (Beval b st); (snd st))    )).

*)

(* Tacticals *)

Ltac uncoerce_basic_H H :=
  repeat (
    simpl in H;
    unfold CTermexp_of_nat in H;
    unfold CTermexp_of_Texp in H;
    unfold PTerm_of_R  in H
    ).

Ltac uncoerce_basic_goal :=
  repeat (
    simpl;
    unfold CTermexp_of_nat;
    unfold CTermexp_of_Texp;
    unfold PTerm_of_R
    ).

Tactic Notation "uncoerce_basic" :=
  uncoerce_basic_goal.

Tactic Notation "uncoerce_basic" ident(H) :=
  uncoerce_basic_H H.


(* ---------- Helper Theorems -------------
 *)

Theorem PAImpliesItself: forall eta : PAssertion, PAImplies eta eta.
Proof. intros. unfold PAImplies. easy. Qed.

Theorem yeqp_inv : forall (y : string) (p : Pterm) (c : Cmd),
      is_analytical_pterm p -> hoare_triple ({{ y = p}}) c ({{ y = p }}).
Proof. intros. eapply HFree. unfold is_analytical. intros. induction p.
        + simpl. rewrite H0. reflexivity.
         + simpl. rewrite H0. reflexivity.
        + simpl. rewrite H0. unfold is_analytical_pterm in H. assert (temp: fst ps1 A = fst ps2 A). apply H. apply H0.
          rewrite temp. simpl. easy.
        +  unfold is_analytical_pterm in H. assert (temp: (Pteval (Psum p1 p2) ps1) = (Pteval (Psum p1 p2) ps2)).
            apply H. apply H0. unfold PTermexp_of_pterm. rewrite temp. simpl. rewrite H0. easy.
        + unfold is_analytical_pterm in H. assert (temp: (Pteval (Pmult p1 p2) ps1) = (Pteval (Pmult p1 p2) ps2)).
            apply H. apply H0. unfold PTermexp_of_pterm. rewrite temp. simpl. rewrite H0. easy.
Qed. 

Theorem eliminate_y: forall (eta1 eta2 : PAssertion) (y : string) (p : Pterm) (c : Cmd),
    is_analytical_pterm p -> p_inv_y p y -> 
      hoare_triple ({{eta1 /\ (y = p)}}) c ({{eta2}}) -> hoare_triple (eta_update_y_p eta1 y p) c (eta_update_y_p eta2 y p).
Proof. intros. 
       assert (H2: hoare_triple ({{y = p}}) c ({{ y = p}})).
        + apply yeqp_inv.
          * easy.
        + assert (H3: hoare_triple ({{eta1 /\ y = p}}) c ({{y = p}})).
          * eapply HConseq. assert (temp: PAImplies ({{eta1 /\ y = p}}) ({{y = p}})). easy. apply temp.
            apply PAImpliesItself. apply H2.
          * assert (H4: hoare_triple ({{eta1 /\ y = p}}) c ({{eta2 /\ y = p}})). eapply HAnd. apply H1. apply H3.
            assert (H10: hoare_triple ({{eta1 /\ y = p}}) c (eta_update_y_p eta2 y p)).
            eapply HConseq. apply PAImpliesItself. assert (H5: PAImplies ({{eta2 /\ y = p }}) (eta_update_y_p eta2 y p)).
            - simpl. unfold eta_update_y_p. unfold PAImplies. intros. unfold pstate_update. destruct H5. unfold PTermexp_of_pterm in H6. rewrite <- H6.
              assert (temp: (y !-> snd ps y; (snd ps)) = snd ps).
              ** apply functional_extensionality. intros. destruct (string_dec x y). rewrite e. apply t_update_eq. apply t_update_neq. symmetry. apply n.
             ** rewrite temp. assert (temp1: (fst ps, snd ps) = ps). destruct ps. simpl. reflexivity. rewrite <- temp1 in H5.  apply H5. 
            - apply H5.
            - apply H4. 
            - eapply HElimv. apply H10. apply H0. unfold eta_inv_y. unfold eta_update_y_p. unfold p_inv_y in H0. intros. rewrite H0 with (r1 := r1) (r2 := r2). unfold pstate_update. simpl. 
              assert (H11 : (y !-> Pteval p (fst ps, y !-> r2; (snd ps)); (y !-> r1; (snd ps))) = (y !-> Pteval p (fst ps, y !-> r2; (snd ps)); (y !-> r2; (snd ps)))).
              ** apply functional_extensionality. intros. destruct (string_dec x y). rewrite e. transitivity (Pteval p (fst ps, y !-> r2; (snd ps))). apply t_update_eq. symmetry. apply t_update_eq.
                 assert (H11: (y !-> r1; (snd ps)) x = (y !-> r2; (snd ps)) x). transitivity ((snd ps) x). apply t_update_neq. symmetry. apply n. 
                  symmetry. apply t_update_neq. symmetry. apply n. transitivity ((y !-> r1; (snd ps)) x). apply t_update_neq. symmetry. apply n.
                  symmetry. rewrite H11. apply t_update_neq. symmetry. apply n.
              ** rewrite H11. easy.
Qed.  

Theorem helper1: forall (P Q R : PAssertion), 
    {{(P /\ Q) /\ R}} = {{P /\ (Q /\ R)}}.
Proof. intros. apply functional_extensionality. intros. simpl. apply propositional_extensionality. easy.
Qed.
                      
Definition trivial_measure: Measure := (fun A : Assertion => 0%R).
Definition trivial_intp : Intp := (fun y : string => 0%R).
Definition trivial_pstate : Pstate := (trivial_measure, trivial_intp).



Theorem proof3_short: forall x : string, hoare_triple probability_measures (TAsgn x (Const 1)) {{ 1 = (prob (1 = x)) }}.
Proof.
  intros. eapply HConseq.
  + assert (H : PAImplies probability_measures  ({{(1 = (prob (1 = x))) [[x t-> 1]] }})).
   - unfold PAImplies. unfold probability_measures. intros. 
     unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold PTerm_of_R. unfold PTerm_of_R in H. rewrite <- H. unfold Pteval. 
     assert (H1 : forall x: string, (fun st : state => (((x !-> 1; fst st) x) = 1)) = \{true\}).
      ++ intros. apply functional_extensionality. intros. rewrite t_update_eq.
      apply propositional_extensionality. easy.
      ++ rewrite H1. reflexivity.
   - apply H. 
  + apply PAImpliesItself. 
  + unfold Pteval. unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold Teval. unfold PTerm_of_R. apply HTAsgn.
Qed.

Theorem proof3_pretty: forall x : string, {{(prob true) = 1}} x := 1 {{ 1 = (prob (1 = x)) }}.
Proof.
  intros. eapply HConseq.
  + assert (H : PAImplies probability_measures  ({{(1 = (prob (1 = x))) [[x t-> 1]] }})).
   - unfold PAImplies. unfold probability_measures. intros. 
     unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold PTerm_of_R. unfold PTerm_of_R in H. rewrite <- H. unfold Pteval. 
     assert (H1 : forall x: string, (fun st : state => (((x !-> 1; fst st) x) = 1)) = \{true\}).
      ++ intros. apply functional_extensionality. intros. rewrite t_update_eq.
      apply propositional_extensionality. easy.
      ++ rewrite H1. reflexivity.
   - apply H. 
  + apply PAImpliesItself. 
  + unfold Pteval. unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold Teval. unfold PTerm_of_R. apply HTAsgn.
Qed.

(* 
Theorem proof1: forall x : string, hoare_triple  {{ (prob true) = 1 }} (TAsgn x (Const 1)) {{ (prob (x = 1)) = 1 }}.
Proof.
  intros. assert (H : {{ ((prob (x = 1)) = 1) [[ x t-> 1]]}} = {{(prob true) = 1}}).
    - unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold probability_measures. 
      apply functional_extensionality. intros. unfold PTerm_of_R.
      assert ((fun st : state => CTermexp_of_nat 1 (x !-> 1; fst st, snd st) = (x !-> 1; fst st) x) = {{true}}).
        + apply functional_extensionality. intros. unfold CTermexp_of_nat. 
          apply propositional_extensionality. split.
          * easy.
          * intros. rewrite t_update_eq. reflexivity.
        + rewrite H. reflexivity.
    - rewrite <- H. assert (H1: hoare_triple  {{(prob (CTermexp_of_Texp (Var x)) = (CTermexp_of_nat 1) = (PTerm_of_R 1)) [[x t-> (Const 1)]]}} (TAsgn x (Const 1)) {{(prob (CTermexp_of_Texp (Var x)) = (CTermexp_of_nat 1)) = (PTerm_of_R 1)}}). 
 simpl.
      assert (H1: forall st: state, (((x !-> 1; (fst st)) x) = 1)   ).
(* (x !-> (1, snd (st x)); st) x = (1, snd (st x))). *)
      + intros. apply t_update_eq.
      + assert (H2: forall st:state, ( (CTermexp_of_nat 1) (x !-> 1; (fst st), snd st)) = ((x !-> 1; (fst st)) x)). 
        (* cant do \{1\} here for some reason *)
        * intros. rewrite H1. replace (CTermexp_of_nat 1) with (fun s:state => 1). easy. easy.
        * apply functional_extensionality. intros. assert (H3: forall P : PAssertion, ) replace (fun st : state =>
     ((CTermexp_of_nat 1) (x !-> 1; (fst st), snd st)) = ((x !-> 1; (fst st)) x)) with (fun st : state => True).
          ** 
      + assert (H2: forall st: state, (fst ((x !-> 1; ((fst st)), (snd st))) x = 1) = True).
        *  intros. rewrite H1. simpl. apply propositional_extensionality. split.
          +++ intros. constructor.
          +++ intros. constructor.
        * assert (H3: (fun st : state => (fst ((x !-> 1; ((fst st)), (snd st))) x = 1)) = (fun _ => True)).
          ++ apply functional_extensionality. apply H2.
          ++ rewrite H3. reflexivity.
    - rewrite <- H. apply HTAsgn.
Qed. *)


(*
Definition probability_measures_long : PAssertion :=       (* All measures that have total measure 1 *)
  fun ps => ((fst ps) (fun st => True)) = 1%R.
*)

(*
Definition probability_measures : PAssertion :=
    {{ (prob true) = 1 }}.
*)


Theorem trivial : forall (P Q : Prop), (P = Q) -> (P <-> Q).
Proof. intros. split.
  - rewrite H. intros. apply H0.
  - rewrite H. auto.
Qed.

(* Theorem proof1: forall x : string, hoare_triple  {{ (prob true) = 1 }} (TAsgn x (Const 1)) {{ (prob (x = 1)) = 1 }}.
Proof. 
  intros. assert (H : tasgn_pt x (Const 1) (fun ps => (fst ps) (fun st => ((fst st) x) = 1) = 1%R) = probability_measures).
  - unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold probability_measures.
    apply functional_extensionality. intros. unfold PTerm_of_R.
    assert (H1 : (fun st : state => fst ((x !-> (1, snd (st x)); st) x) = 1) = fun _ =>True).
    + apply functional_extensionality. intros. rewrite t_update_eq. simpl.
      apply propositional_extensionality. easy.
    + rewrite H1. reflexivity.
  - rewrite <- H. apply HTAsgn.
Qed.
 *)
(* {int (true) = 1} [x := 1] {int (x = 1) = 1}
 *)


(* 
Theorem proof3: forall x : string, hoare_triple probability_measures (TAsgn x (Const 1)) (fun ps => (fst ps) (fun st => ((fst st) x) = 1) = 1%R).
Proof.
  intros. eapply HConseq.
  + assert (H : PAImplies probability_measures (tasgn_pt x (Const 1) (fun ps => (fst ps) (fun st => ((fst st) x) = 1) = 1%R))).
   - unfold PAImplies. unfold probability_measures. intros. 
     unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl. unfold PTerm_of_R in H. rewrite -> H. unfold Pteval. 
     assert (H1 : forall x: string, (fun st : state => (((x !-> 1; fst st) x) = 1)) = {{true}}).
      ++ intros. apply functional_extensionality. intros. rewrite t_update_eq.
      apply propositional_extensionality. easy.
      ++ rewrite H1. reflexivity.
   - apply H. 
  + apply PAImpliesItself. 
  + apply HTAsgn.
Qed. *)

(* {int(true) = 1} [btoss(x, 0,5)] {int(x = True) = 0.5}
 *)

Theorem probtoss_short: forall x : string, {{ (prob true) = 1 }} x toss 0.5 {{ (prob (x)) = 0.5}}.
Proof.
  intros. eapply HConseq.
    + assert (H : PAImplies ({{ (prob true) = 1 }}) (btoss_pt x (0.5)  {{(prob (x)) = 0.5 }})).
      - simpl. unfold PAImplies. intros. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
        unfold PTerm_of_R. 
        assert (H1 : (fun st : state => (x !-> True; snd st) x) = {{true}}).
        ++  apply functional_extensionality. intros. rewrite t_update_eq. simpl. 
           apply propositional_extensionality. easy.
        ++ rewrite H1. assert (H2 : (fun st : state => (x !-> False; snd st) x) = {{false}}).
           * apply functional_extensionality. intros. rewrite t_update_eq. simpl.
             apply propositional_extensionality. split. 
              ** intros. contradiction.
              ** intros. contradiction.
           *  rewrite H2. rewrite empty_set_measure. rewrite H. unfold PTerm_of_R. lra.
      - apply H.
    + apply PAImpliesItself.
    + apply HBToss.
Qed.
 
(* Theorem probtoss: forall x : string, hoare_triple probability_measures (BToss x 0.5) (fun ps => (fst ps) (fun st => snd (st x) = True) = 0.5%R).
Proof.
  intros. eapply HConseq.
    + assert (H : PAImplies probability_measures (btoss_pt x (0.5) (fun ps => (fst ps) (fun st => snd (st x) = True) = 0.5%R))).
      - unfold PAImplies. unfold probability_measures. intros. 
        unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
        assert (H1: (fun st : state => (snd ((x !-> (fst (st x), True); st) x) = True)) = fun _ => True).
        *  apply functional_extensionality. intros. rewrite t_update_eq. simpl. 
           apply propositional_extensionality. easy.
        * rewrite H1. assert (H2: (fun st : state => snd ((x !-> (fst (st x), False); st) x) = True) = fun _ => False).
          ** apply functional_extensionality. intros. rewrite t_update_eq. simpl.
             apply propositional_extensionality. split. 
              ++ intros. rewrite H0. constructor.
              ++ intros. contradiction.
          ** rewrite H2. rewrite empty_set_measure. rewrite H. lra.
      -  apply H.
   + apply PAImpliesItself.
   + apply HBToss.
Qed. *)

Theorem seq_test: forall x a : string, {{ (prob true) = 1 }} x := 1; a b= true {{(prob (a /\ (x = 1))) = 1}}.
Proof.
  intros. eapply HSeq.
    - apply proof3_pretty.
    - eapply HConseq.
      + simpl. unfold PTerm_of_R. unfold CTermexp_of_nat.
        assert (H: PAImplies ((fun st : Pstate => (1%R = fst st (fun st0 : state => fst st0 x = 1)))) ({{((prob (a /\ (x = 1))) = 1) [[ a b-> true ]]}})).
          -- unfold PAImplies. intros. unfold Pteval. simpl. unfold CTermexp_of_nat. unfold PTerm_of_R. unfold basgn_pt.
             unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
             assert ((fun st : state => (a !-> True; snd st) a /\ 1 = fst st x) = (fun st0 : state => fst st0 x = 1)).
             * apply functional_extensionality. intros. apply propositional_extensionality.
               split. intros. easy. intros. split. rewrite t_update_eq. easy. symmetry. apply H0.
             * rewrite H0. symmetry. apply H.
          -- apply H. 
       + apply PAImpliesItself.
       +  apply HBAsgn.
Qed.

Definition a : string := "a".
Definition x : string := "x".

Definition ifprog: Cmd :=
<{
  a toss 0.5;
  if a then x := 1 else x := 2 end
 }>.
Print ifprog.

Lemma pre1: forall (x0 y1 : string) (r : R), {{ (prob true) = r /\ (y1 = r)}} x0 := 1 {{ (prob (x0 = 1)) = y1}}.
Proof. intros. 
        assert (H : PAImplies {{(prob true) = r /\ (y1 = r)}} {{((prob (x0 = 1)) = y1) [[ x0 t-> 1 ]]}}).
        + unfold PAImplies. intros. simpl. simpl in H. unfold tasgn_pt. unfold measure_sub_term. simpl.
          unfold CTermexp_of_nat. Locate "t->". unfold assertion_sub_term. 
          assert (H1 : (fun st : state => 1 = fst (x0 !-> Teval (Const 1) st; fst st, snd st) x0) = {{true}}).
          -  apply functional_extensionality. intros. simpl. rewrite t_update_eq. 
             apply propositional_extensionality. easy.
          -  rewrite <- H1 in H. unfold PTerm_of_R in H. transitivity r.
              * apply H.
              * symmetry. apply H.
        + eapply HConseq.
          - apply H.
          - apply PAImpliesItself.
          - apply HTAsgn.
Qed.

Lemma pre2: forall (x0 y2 : string), {{ (prob true) = 0.5 /\ (y2 = 0)}} x0 := 2 {{ (prob (x0 = 1)) = y2}}.
Proof. intros.
       assert (H : PAImplies {{(prob true) = 0.5 /\ (y2 = 0)}} {{((prob (x0 = 1)) = y2) [[ x0 t-> 2 ]]}}).
        + unfold PAImplies. intros. simpl. simpl in H. unfold tasgn_pt. unfold measure_sub_term. simpl.
          unfold CTermexp_of_nat. Locate "t->". unfold assertion_sub_term. 
          assert (H1 : (fun st : state => 1 = fst (x0 !-> Teval 2 st; fst st, snd st) x0) = {{false}}).
          -  apply functional_extensionality. intros. simpl. rewrite t_update_eq. 
             apply propositional_extensionality. easy.
          - assert (H2: fst ps (fun st : state => 1 = fst (x0 !-> Teval 2 st; fst st, snd st) x0) = 0%R).
            * rewrite H1. apply empty_set_measure.
            * transitivity 0%R. apply H2. symmetry. apply H.
        + eapply HConseq.
          - apply H.
          - apply PAImpliesItself.
          - apply HTAsgn.
Qed.

Theorem ifthentest: forall (b y1 y2 z : string), {{((prob true) = 0.5 /\ (y1 = 0.5)) / (b) \ ((prob true) = 0.5 /\ (y2 = 0))}}
            <{
  if b then z := 1 else z := 2 end
 }> {{ (y1 + y2) = (prob (z = 1)) }}.
Proof. intros. eapply HIfThen. 
        - simpl. eapply HConseq.
          + assert (H: PAImplies ((fun st : Pstate => fst st {{true}} = PTerm_of_R 0.5 st /\ snd st y1 = PTerm_of_R 0.5 st)) {{(((prob true) = 0.5) /\ (y1 = 0.5))}}).
            *  unfold PAImplies. intros. simpl. apply H.
            * apply H.
          + assert (H : PAImplies ({{ ((prob (z = 1)) = y1) }}) ((fun ps : Pstate => snd ps y1 = fst ps (fun st : state => CTermexp_of_nat 1 st = fst st z)))).
            * unfold PAImplies. intros. simpl. simpl in H. symmetry. apply H.
            * apply H.
          +  apply pre1.
        - simpl. eapply HConseq.
          + assert (H: PAImplies ((fun st : Pstate => fst st {{true}} = PTerm_of_R 0.5 st /\ snd st y2 = PTerm_of_R 0 st)) {{(prob true) = 0.5 /\ (y2 = 0)}}).
              *  unfold PAImplies. intros. simpl. apply H.
            * apply H.
          + assert (H : PAImplies ({{ (prob (z = 1)) = y2}}) ((fun ps : Pstate => snd ps y2 = fst ps (fun st : state => CTermexp_of_nat 1 st = fst st z)))).
            *  unfold PAImplies. intros. simpl. symmetry. apply H.
            * apply H.
          + apply pre2.
Qed. 

Theorem ifthen: forall (b y1 y2 z : string), {{ (((prob b) = 0.5) /\ (((prob (~ b)) = 0.5) /\ (y1 = 0.5))) /\ (y2 = 0) }}
                    <{
  if b then z := 1 else z := 2 end
 }> {{ (y1 + y2) = (prob (z = 1)) }}.
Proof. intros. eapply HConseq.
  + assert (H : PAImplies {{ (((prob b) = 0.5) /\ (((prob (~ b)) = 0.5) /\ (y1 = 0.5))) /\ (y2 = 0) }} {{((prob true) = 0.5 /\ (y1 = 0.5)) / (b) \ ((prob true) = 0.5 /\ (y2 = 0))}}).
    -  simpl. unfold PAImplies. intros. simpl. Locate "P / b \ Q" . unfold psfBpsf. Locate "P / B". unfold PAcondB. unfold Measure_cond_B. simpl.
        unfold PTerm_of_R. unfold PTerm_of_R in H. unfold CBoolexp_of_bexp in H. simpl in H. split.
      * split. simpl. replace (fun st : state => True /\ snd st b) with (fun st : state => snd st b). apply H.
        apply functional_extensionality. intros. apply propositional_extensionality. easy. apply H.
      * split. simpl. replace (fun st : state => True /\ ~ snd st b) with (fun st : state => ~ snd st b). apply H.
        apply functional_extensionality. intros. apply propositional_extensionality. easy. apply H.
    -  apply H.
  + apply PAImpliesItself.
  + apply ifthentest.
Qed.

Theorem trial: forall y : string, (y++"a")%string <> y.
Proof. intros. apply String.eqb_neq. induction y. easy. simpl. rewrite IHy. destruct (Ascii.eqb a0 a0). reflexivity. reflexivity.
Qed.

Theorem intermediary: forall (b y1 z : string),  {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5)}}
                    <{
  if b then z := 1 else z := 2 end
 }> {{ y1 = (prob (z = 1)) }}.
Proof. intros. eapply HConseq.
        assert (H1: forall (y2 : string), y2 <> y1 -> PAImplies ({{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5)}}) (eta_update_y_p ({{((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5)}}) (y2) (0%R))).
        + intros. unfold PAImplies. intros. simpl. unfold eta_update_y_p. simpl. unfold CBoolexp_of_bexp. unfold PTerm_of_R. split. apply H0.
          split. apply H0. transitivity ((snd ps) y1). apply t_update_neq. apply H. apply H0. 
        + apply H1 with (y2 := (y1++"a")%string). apply trial.
        + assert (H2: forall y2 : string, y2 <> y1 -> PAImplies (eta_update_y_p ({{ (y1 + y2) = (prob (z = 1)) }}) (y2) (Preal 0)) {{y1 = (prob (z = 1))}}).
          * intros. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. unfold PAImplies. intros. simpl. unfold PTermexp_of_pterm in H0. unfold Pteval in H0. simpl in H0.
            unfold CTermexp_of_nat in H0. unfold CTermexp_of_nat. assert (H1: ((((y2 !-> 0; (snd ps)) y1) + ((y2 !-> 0; (snd ps)) y2))%R) = snd ps y1).
            ** rewrite t_update_eq. rewrite t_update_neq. lra. easy.
            ** rewrite <- H1. easy.
          * apply H2 with (y2 := (y1++"a")%string). apply trial.
        + eapply eliminate_y.
          * easy.
          * easy.
          * apply ifthen with (b := b) (y1 := y1) (z := z) (y2 := (y1 ++ "a")%string).
Qed.

Theorem ifthenpretty1: forall (b z : string), {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5)}}
      <{
  if b then z := 1 else z := 2 end
 }> {{ (prob (z = 1)) = 0.5 }}.
Proof. intros. eapply HConseq.
        assert (H1: forall (y1 : string), PAImplies ({{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5)}}) (eta_update_y_p ({{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5)}}) (y1) (0.5%R))).
        + intros. unfold PAImplies. intros. simpl. unfold eta_update_y_p. simpl. unfold CBoolexp_of_bexp. unfold PTerm_of_R.
          split. apply H. apply H.
        + apply H1.
        + assert (H2: forall (y1 : string), PAImplies (eta_update_y_p ({{y1 = (prob (z = 1))}}) (y1) (0.5%R)) ({{ (prob (z = 1)) = 0.5 }})).
          * intros. unfold eta_update_y_p. simpl. unfold CTermexp_of_nat. unfold PTerm_of_R. unfold PAImplies. intros. rewrite t_update_eq in H.
            symmetry. easy.
          * apply H2. 
        + eapply eliminate_y. easy. easy. rewrite helper1. apply intermediary with (b := b) (y1 := "a"%string) (z := z).
Qed.

Definition test_prog :=
  <{ 
  while true do 
    "x1" toss 0.5; 
    "x2" toss 0.5 end
}>.

Definition one_third : R := 1/3.

Definition array1 : (Vector.t (Vector.t R 1) 1) := [([0.25%R])].
Definition array2 : (Vector.t R 1) := [0.25%R].

Definition finite_set_nonzero {n : nat} (f : Fin.t n) :
  match n return (Fin.t n -> Prop) with
  | 0 => fun p => False
  | _ => fun _ => True
end f.
Proof. destruct f. auto. auto. Qed.

Definition finiteset_1 {n : nat} (f : Fin.t n) :
  match n return (Fin.t n -> Prop) with
  | 1 => fun p => p = Fin.F1
  | _ => fun _ => True
end f.
Proof. destruct f. 
    - destruct n. auto. auto.
    - destruct n. exfalso. apply (finite_set_nonzero f). easy.
Qed.

Theorem Fin1_is_singleton : forall a : Fin.t 1, a = Fin.F1.
Proof. intros. apply (finiteset_1 a0). Qed.

Theorem whiletest1: forall (x1 x2 y: string), (x1 <> x2) -> (x1 <> y) -> {{ ((prob ((x1 /\ x2) /\ (x1 /\ x2))) <= y) /\ ((prob ((x1 /\ x2) /\ (x1 /\ x2))) = (prob true)) }}
<{ 
  while (x1 /\ x2) do 
    x1 toss 0.5; 
    x2 toss 0.5 end
}> {{ (prob (x1 /\ ~ x2)) <=  (one_third*y) }}.
Proof. intros x1 x2 y Z1 Z2.
       assert (H: forall (b : bexp) (tempA : Assertion), ((b = (And (BVar x1) (BVar x2))) -> (Assertion_equiv tempA (CBoolexp_of_bexp (And (BVar x1) (BVar x2)))) -> 
({{ ((prob (b /\ tempA)) <= y) /\ ((prob (b /\ tempA)) = (prob true)) }}
<{ 
  while (b) do 
    x1 toss 0.5; 
    x2 toss 0.5 end
}> {{ (prob (x1 /\ ~ x2)) <=  (one_third*y) }}))).
      + intros. eapply HWhileUB.
        ++ assert (T: forall st : state, (Beval b st) -> (vector_to_disj 1 ((fun st1 => Beval b st1) :: []) st)).
          * intros. simpl. auto. 
          * exact T.
        ++ assert (forall (i : nat) (_ : Peano.lt i 1),
hoare_triple
  (List.nth i
     (to_list
        (map int_true_eq_one
           (cons (forall _ : state, Prop) (fun st1 : state => Beval b st1) 0
              (nil (forall _ : state, Prop))))) (fun _ : Pstate => True))
  (CSeq (BToss x1 0.5) (BToss x2 0.5))
  (List.nth i
     (to_list
        (antecedent_leq
           (cons (forall _ : state, Prop) (fun st1 : state => Beval b st1) 0
              (nil (forall _ : state, Prop))) [([0.25%R])] (CBoolexp_of_bexp b)
           (fun st : state =>
            and (CBoolexp_of_bexp (BVar x1) st) (not (CBoolexp_of_bexp (BVar x2) st)))
           [0.25%R])) (fun _ : Pstate => True))).
          * intros. destruct i. simpl. unfold int_true_eq_one. unfold apply_func. unfold inner_conj_leq. unfold gamma_leq. simpl.
            unfold gamma_leq. unfold gamma_compare. unfold PTermexp_of_pterm. unfold PTerm_of_R. unfold Pteval. unfold CBoolexp_of_bexp.
            (* simpl. replace i with (Fin.F1 : Fin.t 1). simpl. unfold int_true_eq_one. unfold antecedent_leq. simpl.
            unfold CBoolexp_of_bexp. rewrite H. simpl. unfold inner_conj_leq. unfold zip_gamma_leq.
            unfold zip_gamma_compare. unfold gamma_leq. unfold gamma_compare. unfold zip. unfold PTermexp_of_pterm. unfold PTerm_of_R.
            unfold Pteval. simpl. *)
            ** eapply HConseq. rewrite H. unfold Beval.
              - assert (T: PAImplies
  (fun st : Pstate =>
   and (eq (fst st (fun st1 : state => and (snd st1 x1) (snd st1 x2))) 1%R)
     (eq (fst st (fun st1 : state => and (snd st1 x1) (snd st1 x2)))
        (fst st (fun _ : state => True)))) 
  {{((prob (true)) = 1)}} ). unfold PAImplies. intros. simpl. simpl in H1. transitivity (fst ps (fun st1 : state => and (snd st1 x1) (snd st1 x2))).
   symmetry. apply H2. apply H2. apply T.
              - rewrite H. unfold Beval. assert (T: PAImplies ({{ (((prob (x1 /\ x2)) <= 0.25) /\ ((prob (x1 /\ (~ (x2)))) <= 0.25))}})
  (fun ps : Pstate =>
   and (and (Rle (fst ps (fun st1 : state => and (snd st1 x1) (snd st1 x2))) 0.25) True)
     (Rle
        (fst ps
           (fun st : state =>
            and (not (and (snd st x1) (snd st x2))) (and (snd st x1) (not (snd st x2))))) 0.25))). 
            unfold PAImplies. intros. split. split. apply H2. easy. unfold Pteval in H1. 
            assert (T1: (fst ps
          (fun st : state => (CBoolexp_of_bexp (BVar x1) st) /\ (~ (CBoolexp_of_bexp (BVar x2) st))))
                        = (fst ps (fun st : state => (~ ((snd st x1) /\ (snd st x2))) /\ ((snd st x1) /\ (~ (snd st x2)))))).
            apply equivalence. unfold Assertion_equiv. intros. simpl. split. easy. easy. rewrite <- T1. apply H2. apply T.
              - eapply HSeq. assert (T: {{(prob true) = 1}} x1 toss 0.5 {{(prob x1) = 0.5}}). apply probtoss_short. apply T.
                eapply HConseq. 
                +++ assert (T: PAImplies (fun st : Pstate => (Pteval (Pint (CBoolexp_of_bexp (BVar x1))) st) = (PTerm_of_R 0.5 st)) (btoss_pt x2 0.5 (fun st : Pstate =>
   (((Pteval
        (Pint
           (fun st0 : state => (CBoolexp_of_bexp (BVar x1) st0) /\ (CBoolexp_of_bexp (BVar x2) st0)))
        st) <= (PTerm_of_R 0.25 st))%R) /\
   (((Pteval
        (Pint
           (fun st0 : state =>
            (CBoolexp_of_bexp (BVar x1) st0) /\ (~ (CBoolexp_of_bexp (BVar x2) st0)))) st) <=
     (PTerm_of_R 0.25 st))%R))) ). unfold PAImplies. intros. simpl. unfold btoss_pt. unfold measure_sub_btoss. unfold PTerm_of_R. unfold measure_sub_bexp.
      unfold assertion_sub_bexp. unfold Beval. simpl. 
      replace ((fun st : state => ((x2 !-> True; (snd st)) x1) /\ ((x2 !-> True; (snd st)) x2))) with ((fun st : state => ((snd st) x1))).
      replace ((fun st : state => ((x2 !-> False; (snd st)) x1) /\ ((x2 !-> False; (snd st)) x2))) with ((fun st : state => False)).
      replace ((fun st : state => ((x2 !-> True; (snd st)) x1) /\ (~ ((x2 !-> True; (snd st)) x2)))) with (fun st : state => False).
      replace ((fun st : state => ((x2 !-> False; (snd st)) x1) /\ (~ ((x2 !-> False; (snd st)) x2)))) with ((fun st : state => ((snd st) x1))).
      simpl. rewrite empty_set_measure. unfold Pteval in H2. unfold CBoolexp_of_bexp in H2. unfold Beval in H2. unfold PTerm_of_R in H2. rewrite H2. lra.
        try apply functional_extensionality. intros. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. easy. symmetry. apply Z1.
        apply functional_extensionality. intros. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality. easy. symmetry. apply Z1.
        apply functional_extensionality. intros. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality; easy; symmetry; apply Z1. symmetry. apply Z1.
        apply functional_extensionality. intros. rewrite t_update_neq. rewrite t_update_eq. apply propositional_extensionality; easy; symmetry; apply Z1. symmetry. apply Z1.
        apply T. 
            +++ apply PAImpliesItself.
            +++ apply HBToss.

            ** exfalso. assert (T: ~ ((S i) < 1)). intros. lia. contradiction. 
                (* auto. apply Nat.ltb_lt in H1. . order. apply H2 in H1. easy. assert (forall k : nat, ~ ((S k) < 1)).
                intros K. induction K. apply (PeanoNat.Nat.ltb_lt 1 1).  easy. contradiction. symmetry. apply Fin1_is_singleton. *)
          * apply H1.
        ++ assert (T2: forall i : nat, (i < 1) -> lin_ineq i [one_third] [([0.25%R])] [0.25%R]).
          * intros. destruct i. unfold lin_ineq. simpl. unfold one_third. lra. assert (T: ~ ((S i) < 1)). lia. contradiction.
(*            replace i with (Fin.F1 : Fin.t 1). unfold lin_ineq. simpl. unfold one_third. lra. symmetry. apply Fin1_is_singleton.   *)
          * apply T2.        
        ++ assert (0 < 1). lia. apply H1.
        ++ intros. simpl. rewrite H. unfold Assertion_equiv in H0. symmetry. apply H0.
        ++  simpl. reflexivity.
(*           * intros.  simpl. symmetry. rewrite H. apply H0.
          * apply T3.
        ++ simpl. reflexivity. *)
      + assert (T4: ({{(y >= (prob ((<{ (x1 /\ x2) }>) /\ (<{ (x1 /\ x2) }>)))) /\ ((prob ((<{ (x1 /\ x2) }>) /\ (<{ (x1 /\ x2) }>))) = (prob (true)))}} 
      while <{ (x1 /\ x2) }> do x1 toss 0.5; x2 toss 0.5 end {{(one_third * y) >= (prob (x1 /\ (~ x2)))}})). apply H. easy. easy.
      apply T4.
Qed.  

Theorem whiletest2: forall (x1 x2 y: string), (x1 <> x2) -> (x1 <> y) -> {{ ((prob ((x1) /\ (x1 /\ x2))) <= y) /\ ((prob ((x1) /\ (x1 /\ x2))) = (prob true)) }}
<{ 
  while (x1) do 
    x1 toss 0.5; 
    x2 toss 0.5 end
}> {{ (prob (~ x1 /\ ~ x2)) <=  (0.5*y) }}.
Proof. intros. eapply HWhileUB.
      + assert (T: forall st : state, (Beval (BVar x1) st) -> ((vector_to_disj 2 [fun st1 => Beval (And (BVar x1) (BVar x2)) st1; fun st1 => Beval (And (BVar x1) (Not (BVar x2))) st1]) st)).
        * intros. unfold vector_to_disj. simpl. simpl in H1. tauto.
        * apply T.
      + assert (T: forall (i : nat) (_ : Peano.lt i 2),
hoare_triple
  (List.nth i
     (to_list
        (map int_true_eq_one
           (cons (forall _ : state, Prop)
              (fun st1 : state => Beval (And (BVar x1) (BVar x2)) st1) 1
              (cons (forall _ : state, Prop)
                 (fun st1 : state =>
                  Beval (And (BVar x1) (Not (BVar x2))) st1) 0
                 (nil (forall _ : state, Prop))))))
     (fun _ : Pstate => True)) (CSeq (BToss x1 0.5) (BToss x2 0.5))
  (List.nth i
     (to_list
        (antecedent_leq
           (cons (forall _ : state, Prop)
              (fun st1 : state => Beval (And (BVar x1) (BVar x2)) st1) 1
              (cons (forall _ : state, Prop)
                 (fun st1 : state =>
                  Beval (And (BVar x1) (Not (BVar x2))) st1) 0
                 (nil (forall _ : state, Prop)))) 
           [([0.25%R; 0.25%R]); ([0.25%R; 0.25%R])] (CBoolexp_of_bexp (BVar x1))
           (fun st : state =>
            and (not (CBoolexp_of_bexp (BVar x1) st))
              (not (CBoolexp_of_bexp (BVar x2) st))) 
           [0.25%R; 0.25%R])) (fun _ : Pstate => True))). 
            * intros. destruct i.
                -  simpl. unfold int_true_eq_one. unfold antecedent_leq. unfold apply_func. unfold inner_conj_leq. unfold gamma_leq. simpl.
            unfold gamma_leq. unfold gamma_compare. unfold PTermexp_of_pterm. unfold PTerm_of_R. unfold Pteval. unfold CBoolexp_of_bexp. admit.
                - destruct i. simpl. unfold int_true_eq_one. unfold antecedent_leq. unfold apply_func. unfold inner_conj_leq. unfold gamma_leq. simpl.
            unfold gamma_leq. unfold gamma_compare. unfold PTermexp_of_pterm. unfold PTerm_of_R. unfold Pteval. unfold CBoolexp_of_bexp. admit.
            assert (T: ~ (S (S i) < 2)). lia. contradiction.
        * apply T.
    + simpl. unfold int_true_eq_one. unfold antecedent_leq. unfold apply_func. unfold inner_conj_leq. unfold gamma_leq. simpl.
            unfold gamma_leq. unfold gamma_compare. unfold PTermexp_of_pterm. unfold PTerm_of_R. unfold Pteval. unfold CBoolexp_of_bexp. 
        * simpl. unfold int_true_eq_one. simpl. unfold antecedent_leq. unfold inner_conj_leq. unfold zip_gamma_leq. unfold gamma_leq. unfold gamma_compare. simpl.
          unfold apply_func.
          unfold zip. unfold map. simpl. unfold PAssertion_conj. simpl. unfold zip. unfold to_list. simpl. 
          assert (forall i : nat,
(i < 2) ->
(lin_ineq i [0.5%R; 0.5%R] [([0.25%R; 0.25%R]); ([0.25%R; 0.25%R])] [0.25%R; 0.25%R])).
          -- intros. destruct i. unfold lin_ineq. simpl. lra. destruct i. unfold lin_ineq. simpl. lra.
              assert (T: ~ (S (S i) < 2)). lia. contradiction. 
          -- apply H1.
      + assert (0 < 2). lia. exact H1.
      + intros. simpl. tauto.
      + intros. simpl. reflexivity.
Admitted.

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
(forall st : state, ((List.nth i (to_list [CBoolexp_of_bexp <{x1 /\ (x2 /\ x3) }>; CBoolexp_of_bexp <{~ x1 /\ (~x2 /\ ~x3) }>]) (fun _ : state => True)) st) -> (Beval b st))).
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

Definition b : string := "b".
Definition val : string := "val".

Definition body : Cmd :=
  <{ 
  b toss 0.5;
  if b then val := 2 * val + 1 else val := 2 * val end
}>.


(* Helper Theorems *)


Theorem RigidUnchanged: forall (y: string) (c: Cmd) (r: R), {{ y = r }} c {{ y = r}}.
Proof.
intros. apply HFree.
unfold is_analytical. intros. split. simpl. rewrite -> H. easy. simpl. rewrite -> H. easy.
Qed.

Theorem measure_inclusion_true: forall (mu: Measure) (P: Assertion), ((mu P) <= (mu True))%R.
Proof.
intros. apply measure_inclusion. intros. easy.
Qed.


Theorem measure_false_is_zero: forall (mu: Measure), ((mu ({{false}})) = 0)%R.
Proof.
intros. pose proof measure_true_dest mu (\{ true \}).
        assert (((mu \{ ~ true \}) = 0)%R). lra.
        assert  (mu \{ ~ true \} = mu ({{ false }})). apply equivalence. easy.
        rewrite <- H1. easy.
Qed.

Theorem measure_leq0_implies_eq0: forall (mu: Measure) (P:Assertion), ((mu P) <= 0)%R -> ((mu P) = 0)%R.
Proof.
intros. pose proof (positive mu P) as H1. apply Rle_antisym. easy. apply Rge_le in H1. exact H1.
Qed.

Theorem empty_measure_inclusion: forall (mu:Measure), ((mu True) = 0)%R -> (forall (P: Assertion), ((mu P) = 0)%R).
Proof.
intros. assert (forall st : state, (P st) -> (assert_of_Prop True st)). intros. easy. pose proof measure_inclusion mu P (\{True\}) as H1.
pose proof H1 H0. rewrite -> H in H2. pose proof measure_leq0_implies_eq0 mu P. pose proof H3 H2. assumption.
Qed.

(* Idk if I used the other version *)
Theorem empty_measure_inclusion2: forall (mu:Measure) (P: Assertion), ((mu True) = 0)%R ->  ((mu P) = 0)%R.
Proof.
intros. assert (forall st : state, (P st) -> (assert_of_Prop True st)). intros. easy. pose proof measure_inclusion mu P (\{True\}) as H1.
pose proof H1 H0. rewrite -> H in H2. pose proof measure_leq0_implies_eq0 mu P. pose proof H3 H2. assumption.
Qed.

Theorem HConseqLeft: forall (eta1 eta2 eta3: PAssertion) (c: Cmd), PAImplies eta1 eta2 ->  hoare_triple eta2 c eta3 -> hoare_triple eta1 c eta3.
Proof.
intros. apply HConseq with (eta2 := eta2) (eta3 := eta3). easy. easy. easy. Qed.

Theorem HConseqRight: forall (eta1 eta2 eta3: PAssertion) (c: Cmd), PAImplies eta2 eta3 ->  hoare_triple eta1 c eta2 -> hoare_triple eta1 c eta3.
Proof.
intros. apply HConseq with (eta2 := eta1) (eta3 := eta2). easy. easy. easy. Qed.

Theorem AddRigidLeft: forall (y: string) (r: R) (eta1 eta2: PAssertion) (c: Cmd), hoare_triple eta1 c eta2 -> 
            hoare_triple (fun ps => eta1 ps /\ ((snd ps) y) = r) c eta2.
Proof.
intros. apply HConseqLeft with (eta2 := eta1). 2: easy. unfold PAImplies. intros. easy. Qed.

Theorem AddAndLeft: forall (eta1 eta2 eta3: PAssertion) (c: Cmd), hoare_triple eta2 c eta3 -> ({{ eta1 /\ eta2 }} c {{ eta3}}).
Proof.
intros. apply HConseqLeft with (eta2:= ({{eta2}})). easy. easy. Qed.

Theorem FlipAndLeft: forall (eta1 eta2 eta3: PAssertion) (c: Cmd), ({{ eta1 /\ eta2 }} c {{ eta3}}) -> ({{ eta1 /\ eta2 }} c {{ eta3}}).
Proof.
intros. apply HConseqLeft with (eta2:= ({{eta1 /\ eta2}})). easy. easy. Qed.

Theorem FlipAndRight: forall (eta1 eta2 eta3: PAssertion) (c: Cmd), ({{ eta1 }} c {{ eta2 /\ eta3 }}) -> ({{ eta1 }} c {{ eta3 /\ eta2}}).
Proof.
intros. apply HConseqRight with (eta2:= ({{eta2 /\ eta3}})). easy. easy. Qed.

Theorem AddRigidBoth: forall (y: string) (r: R) (eta1 eta2: PAssertion) (c: Cmd), hoare_triple eta1 c eta2 -> 
            hoare_triple   (fun ps => eta1 ps /\ ((snd ps) y) = r) c (fun ps => eta2 ps /\ ((snd ps) y) = r).
Proof.
intros. pose proof AddRigidLeft y r eta1 eta2 c. pose proof RigidUnchanged y c r. uncoerce_basic H1. pose proof H0 H. apply HAnd. easy.
apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y = r)). easy. easy. Qed.


Theorem AddRigidRight: forall (y: string) (r: R) (eta1 eta2: PAssertion) (c: Cmd), hoare_triple ({{eta1 /\ (y = r)}}) c eta2 -> 
            hoare_triple   ({{eta1 /\ (y = r)}}) c ({{eta2 /\ (y = r)}}).
Proof.
intros. apply HAnd. easy. apply HConseqLeft with (eta2 := {{(y = r)}}). easy. apply RigidUnchanged. Qed.

Theorem AddTrue: forall (mu: Measure) (P Q: Assertion), ((mu P) = (mu \{ true \}))%R -> ((mu Q) = (mu \{ P /\ Q \}))%R.
Proof.
intros. apply Rle_antisym. 
- replace (mu Q) with (mu (\{(P /\ Q) \/ ( (~P) /\ Q) \})).
  replace (mu (\{(P /\ Q) \/ ( (~P) /\ Q) \})) with ((mu (\{ P /\ Q \})) + (mu (\{ (~P) /\ Q \})))%R.
  replace (((mu (fun st : state => (P st) /\ (Q st))) +
  (mu (fun st : state => (~ (P st)) /\ (Q st)))) <=
 (mu (fun st : state => (P st) /\ (Q st))))%R with (((mu (fun st : state => (~ (P st)) /\ (Q st)))) <=
 0)%R. 
 -- assert (((mu \{~P\}) = 0)%R). apply measure_P_eq_true. easy. rewrite <- H0. apply measure_inclusion. easy. 
 -- apply propositional_extensionality. split. lra. lra.
 -- apply fin_additivity. easy.
 -- apply equivalence. unfold Assertion_equiv. intros. split. intros. destruct H0. easy. easy. intros. destruct (classic (P st)); tauto.
    
  
- apply measure_inclusion. easy.
Qed. 


 



  

End PHL.

