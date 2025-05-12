(*Testing out stuff for Probabilistic Hoare Logic project *)

From PLF Require Import Maps.
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

(* Import ListNotations. *)

Module PHL.

(* Defining terms over nat for now
 *)
Inductive Term: Type :=
  | Const (c : nat)
  | Var (x : string)
  | sum (t1 : Term) (t2 : Term)
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


Definition gamma_leq := (fun (gamma: Assertion) (r: R) =>  (fun (st: Pstate) => ((( PTermexp_of_pterm (Pint gamma)) st) <= ((PTerm_of_R r) st))%R)).
Definition gamma_geq := (fun (gamma: Assertion) (r: R) =>  (fun (st: Pstate) => ((( PTermexp_of_pterm (Pint gamma)) st) >= ((PTerm_of_R r) st))%R)).
Definition gamma_eq := (fun (gamma: Assertion) (r: R) =>  (fun (st: Pstate) => ((( PTermexp_of_pterm (Pint gamma)) st) = ((PTerm_of_R r) st))%R)).


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


Definition antecedent_leq {n: nat} (i: Fin.t n) (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n) : PAssertion :=
    fun ps => ((inner_conj_leq gammas (Vector.nth r2 i)) ps) /\ ((gamma_leq (\{ (~beta) /\ gamma \}) (Vector.nth r1 i) ) ps) . 


Fixpoint vector_sum {n: nat} (X: Vector.t R n) : R :=
  match X with
  | [] => 0%R
  | hd:: tl => (hd + vector_sum tl)%R 
end.


Definition lin_ineq {n: nat} (i: Fin.t n) (X: Vector.t R n) (r2: Vector.t (Vector.t R n) n) (r1: Vector.t R n) : Prop :=
     Rle (Vector.nth X i)  ((vector_sum (zip Rmult (Vector.nth r2 i) (X))) + (Vector.nth r1 i))%R. 


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
  
  | HWhile : forall (m : nat) (beta gamma: Assertion) (s : Cmd) (G : Vector.t Assertion m) (X : Vector.t R m) (P : Vector.t (Vector.t R m) m) (T : Vector.t R m),
      (forall st, beta st -> (vector_to_disj m G) st) -> (forall (i : Fin.t m), hoare_triple (int_true_eq_one (Vector.nth G i)) s (antecedent_leq i G P beta gamma  T)) 
      -> (forall (i: Fin.t m), lin_ineq i X P T)
      -> (forall (i: Fin.t m) (y: string), 
              hoare_triple (fun ps =>  (int_true_leq_R 
                        (fun st => (beta st) /\ ((Vector.nth G i) st)) 
                    ((snd ps) y)) ps) s (fun ps => ( gamma_leq gamma (Rmult (Vector.nth X i) ((snd ps) y))) ps)
          )
. 
  


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


Theorem ifthenpretty: forall (b y1 y2 z : string), y1<>y2 -> {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5)}}
      <{
  if b then z := 1 else z := 2 end
 }> {{ (prob (z = 1)) = 0.5 }}.
Proof. intros b y1 y2 z. intros H20.
        assert (H : {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5) /\ (y2 = 0) }}  
                      <{
  if b then z := 1 else z := 2 end
 }> {{ (y1 = 0.5) /\ (y2 = 0) }}).
  - assert (H1 :{{ (y1 = 0.5) /\ (y2 = 0) }}  <{
  if b then z := 1 else z := 2 end
 }> {{ (y1 = 0.5) /\ (y2 = 0) }}).
    + eapply HFree. simpl. unfold is_analytical. intros. unfold PTerm_of_R. rewrite H. easy.
    + eapply HConseq.
      * assert (PAImplies {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5) /\ (y2 = 0) }} {{ (y1 = 0.5) /\ (y2 = 0) }}).
        ** unfold PAImplies. intros. split. apply H. apply H.
        ** apply H.
      * apply PAImpliesItself.
      * apply H1.
  - assert (H1: {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5) /\ (y2 = 0) }}  
                      <{
  if b then z := 1 else z := 2 end
 }> {{ (y1 + y2 = (prob (z = 1))) /\ ((y1 = 0.5) /\ (y2 = 0))  }}).
      + eapply HAnd. 
        * apply ifthen.
        *  apply H.
      + assert (H2: {{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) /\ (y1 = 0.5) /\ (y2 = 0) }}  
                      <{
  if b then z := 1 else z := 2 end
 }> {{ 0.5 = (prob (z = 1))  }}).
          * eapply HConseq.
            ** apply PAImpliesItself.
            ** assert (PAImplies {{(y1 + y2 = (prob (z = 1))) /\ ((y1 = 0.5) /\ (y2 = 0))}} {{0.5 = (prob (z = 1)) }}).
              -- unfold PAImplies. intros st. simpl. unfold PTerm_of_R. unfold CTermexp_of_nat. intros. destruct H0.
                 destruct H2. rewrite H2 in H0. rewrite H3 in H0. rewrite <- H0. lra.
              -- apply H0.
            **  apply H1.
          * assert (H3 :{{((prob b) = 0.5) /\ (((prob (~ b)) = 0.5) /\ (y1 = 0.5))}} 
     if b then z := 1 else z := 2 end {{0.5 = (prob (z = 1))}}).
            ** eapply HConseq. 
              assert (H4: PAImplies (fun st : Pstate =>
   ((Pteval (Pint (CBoolexp_of_bexp (BVar b))) st) = (PTerm_of_R 0.5 st)) /\
   (((Pteval (Pint (fun st0 : state => ~ (CBoolexp_of_bexp (BVar b) st0))) st) =
     (PTerm_of_R 0.5 st)) /\ ((PTermexp_of_pterm (Pvar y1) st) = (PTerm_of_R 0.5 st)))) 
  (eta_update_y_p ({{(((prob b) = 0.5) /\ (((prob (~ b)) = 0.5) /\ (y1 = 0.5)))}}) (y2) (Preal 0%R))).
                *** simpl. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. unfold CBoolexp_of_bexp. 
                    unfold PTerm_of_R. simpl. unfold PAImplies. intros. simpl. split. apply H0. rewrite t_update_neq.
                    apply H0. symmetry. apply H20.
                *** apply H4.
                *** apply PAImpliesItself.
                *** eapply HElimv.
                  ++ simpl. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold CTermexp_of_nat. 
                     unfold CBoolexp_of_bexp in H2. unfold CTermexp_of_nat in H2. unfold Pteval in H2. unfold Beval in H2.
                     unfold PTerm_of_R in H2. unfold PTermexp_of_pterm in H2. unfold CTermexp_of_Texp in H2. unfold Teval in H2.
                     unfold Pteval in H2. unfold Beval. replace  (fun ps : Pstate =>
   and
     (and (eq (fst ps (fun st : state => snd st b)) 0.5%R)
        (and (eq (fst ps (fun st : state => not (snd st b))) 0.5%R) (eq (snd ps y1) 0.5%R)))
     (eq (snd ps y2) 0%R)) with  (fun st : Pstate =>
        and (eq (fst st (fun st0 : state => snd st0 b)) 0.5%R)
          (and (eq (fst st (fun st0 : state => not (snd st0 b))) 0.5%R)
             (and (eq (snd st y1) 0.5%R) (eq (snd st y2) 0%R)))).
                      +++ apply H2.
                      +++ apply functional_extensionality. intros. simpl. apply propositional_extensionality.
                          split. easy. easy.
                  ++ unfold p_inv_y. easy.
                  ++ unfold eta_inv_y. easy.
               ** eapply HConseq.
                  *** assert (H4: PAImplies  (fun st : Pstate =>
   ((Pteval (Pint (CBoolexp_of_bexp (BVar b))) st) = (PTerm_of_R 0.5 st)) /\
   ((Pteval (Pint (fun st0 : state => ~ (CBoolexp_of_bexp (BVar b) st0))) st) = (PTerm_of_R 0.5 st))) (eta_update_y_p ({{ ((prob b) = 0.5) /\ ((prob (~ b)) = 0.5) }}) (y1) (Preal 0.5%R))).
-- simpl. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. unfold CBoolexp_of_bexp. 
                    unfold PTerm_of_R. simpl. unfold PAImplies. intros. simpl. split. apply H0. apply H0.
                -- apply H4.
                *** apply PAImpliesItself.
                *** eapply HElimv.
                  ++ simpl. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold CTermexp_of_nat. 
                     unfold CBoolexp_of_bexp in H3. unfold CTermexp_of_nat in H3. unfold Pteval in H3. unfold Beval in H3.
                     unfold PTerm_of_R in H3. unfold PTermexp_of_pterm in H3. unfold CTermexp_of_Texp in H3. unfold Teval in H3.
                     unfold Pteval in H3. unfold Beval. replace (fun st : Pstate => (fst st (fun st0 : state => 1 = (fst st0 z))) = (0.5%R)) with (fun st : Pstate => (0.5%R) = (fst st (fun st0 : state => 1 = (fst st0 z)))).
                        +++ rewrite helper1. apply H3.
                        +++ apply functional_extensionality. intros. apply propositional_extensionality. easy.
                  ++ easy. 
                  ++ easy.
Qed.



 

(* Defining syntax of Probabilistic state formula *)

Inductive Psf : Type :=
  | PsfT 
  | PsfF
  | Psfleq (t1 : Pterm) (t2 : Pterm)
  | Psfnot (f1 : Psf)
  | Psfor (f1 : Psf) (f2 : Psf)





(* Function to evaluate psf *)

(* Fixpoint Psfeval (f : Psf) (mu : Measure) (rho : Intp) : Prop :=
  match f with
    | PsfT => True
    | PsfF => False
    | Psfleq t1 t2 => Rle (Pteval t1 mu rho) (Pteval t2 mu rho)
    | Psfnot f => ~ (Psfeval f mu rho)
    | Psfor f1 f2 => (Psfeval f1 mu rho) \/ (Psfeval f2 mu rho)
end. *)



(* Coercions *)
(* Recall - a classical state state:string -> nats*bool*)
Definition CNatexp: Type :=  state -> nat. (* Classical nat exp.*)
Definition CPropexp: Type := state -> Prop. (* Classical  Boolean/Prop exp*)
(* Recall - Assertion := state -> Prop*)
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P. (* P to 'if state satisfies P'*)
Definition CNatexp_of_nat (n: nat) : CNatexp := fun _=> n. (*  n to 'given state st return n'*)
Definition CNatexp_of_Texp (a: Term): CNatexp := fun st => Teval a st. (* evaluate the term on the state *) 

Definition CPropexp_of_Prop (P: Prop): Assertion := fun _ => P.
Definition  CPropexp_of_bexp (b: bexp): CPropexp := fun st => Beval b st. (* evaluate the _boolean_ term on the state *)

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion CNatexp_of_nat : nat >->CNatexp.
Coercion CNatexp_of_Texp : Term >-> CNatexp.

(*Inductive Term: Type :=
  | Const (c : nat)
  | Var (x : string)
  | sum (t1 : Term) (t2 : Term)
  | mult (t1 : Term) (t2 : Term). *)

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.

Notation "a + b" := (fun st => (a:CNatexp) st + (b:CNatexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:CNatexp) st - (b:CNatexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:CNatexp) st * (b:CNatexp) st) (in custom assn at level 40, left associativity) : assertion_scope.
Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

Definition assertion1: CNatexp := (12).
Definition assertion2: CNatexp := 12 + 12.
\u00b8
Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.




Definition Aexp : Type := state -> nat.


End PHL.
