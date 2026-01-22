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

(* Import ListNotations. *)

Module PHL.

(* Changes : Mod; Uniform Dice Roll *)

(* Defining terms over nat
 *)
Inductive Term: Type :=
  | Const (c : nat)
  | Var (x : string)
  | sum (t1 : Term) (t2 : Term)
  | sub (t1 : Term) (t2 : Term)
  | mult (t1 : Term) (t2 : Term)
(* Mod *)
  | modulo (t1 :Term) (t2 : Term).

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


(*Definition of valuation to program variables *)
Definition state := (total_map nat) * (total_map Prop).

(* Evaluating a term in a state *)

Fixpoint Teval (t : Term) (s : state) : nat :=
  match t with
    | Const c => c
    | Var x => (fst s) x
    | sum t1 t2 => (Teval t1 s) + (Teval t2 s)
    | sub t1 t2 => (Teval t1 s) - (Teval t2 s)
    | mult t1 t2 => (Teval t1 s) * (Teval t2 s)
    | modulo t1 t2 => (Teval t1 s) mod (Teval t2 s)
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
(* Mod *)
Notation " x 'mod' y" := (modulo x y) (in custom com at level 40, left associativity): com_scope.

(* bexps - built using term comparisons and boolean operators *)
Coercion BConst : bool >-> bexp.
Coercion BVar : string >-> bexp.
Definition test: bexp := true.
Notation "'true'"  := (BConst true)  (in custom com at level 0) : com_scope.
Notation "'false'" := (BConst false) (in custom com at level 0) : com_scope.
Notation "x <= y" := (Leq (x:Term) (y:Term)) (in custom com at level 60, left associativity): com_scope.
Notation "x >= y" := (Leq y x) (in custom com at level 60, left associativity): com_scope. 
Notation "x = y" := (Eq y x) (in custom com at level 60, left associativity): com_scope. 
Notation "'~' x" := (Not x) (in custom com at level 70, left associativity): com_scope.
Notation "x \/ y" := (Or x y) (in custom com at level 80, left associativity): com_scope.
Notation "x /\ y" := (And x y) (in custom com at level 80, left associativity): com_scope.
Notation "x -> y" := (Implies x y) (in custom com at level 80, left associativity): com_scope.
Notation "x <-> y" := (Iff x y) (in custom com at level 80, left associativity): com_scope.


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

(* Handling CBoolexp_of_bexp *)
Notation "'true'" := (fun st => True) (in custom assn at level 65, right associativity) : passertion_scope.
Notation "'false'" := (fun st => False) (in custom assn at level 65, right associativity) : passertion_scope.
Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 70, right associativity) : passertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : passertion_scope.
Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : passertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : passertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : passertion_scope.

Notation "a + b" := (fun st => ((a:CTermexp) st + (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
Notation "a - b" := (fun st => ((a:CTermexp) st - (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
Notation "a * b" := (fun st => ((a:CTermexp) st * (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
(* Mod *)
Notation "a 'mod' b" := (fun st => ((a:CTermexp) st mod (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope.
Notation "a <= b" := (fun st => ((a:CTermexp) st <= (b:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 
Notation "a >= b" := (fun st => ((b:CTermexp) st <= (a:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 
Notation "a = b" := (fun st => ((b:CTermexp) st = (a:CTermexp) st)%nat) (in custom assn at level 50, left associativity) : passertion_scope. 


(* assertion_sub_term x e P = {set of all states s such that ([x := e] s) satisfies P}
 *)
Definition assertion_sub_term (x : string) (e : Term) (P : Assertion) : Assertion :=
  fun st => ( P ((x !-> (Teval e st); (fst st)),(snd st))). (* REVIEW if this defn is correct *)

(* assertion_sub_bexp x b P = {set of all states s such that ([x := b] s) satisfies P}
 *)
Definition assertion_sub_bexp (x : string) (b : bexp) (P : Assertion) : Assertion :=
  fun st => (P ( (fst st), (x !-> (Beval b st); (snd st))    )).


Notation "P [ X 't->' a ]" := (assertion_sub_term X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : passertion_scope.

Notation "P [ X 'b->' a ]" := (assertion_sub_bexp X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : passertion_scope.

(* Defining a "measure". *)

Definition Measure : Type := Assertion -> R.

(* Axioms for measures *)
Axiom empty_set_measure : forall mu : Measure, mu (fun _ => False) = 0%R.
Axiom equivalence: forall (mu : Measure) (P Q : Assertion), 
                (Assertion_equiv P Q) -> (mu P = mu Q).
Axiom fin_additivity: forall (mu : Measure) (P Q : Assertion), 
    (forall st : state, ~ (P st /\ Q st)) -> 
      ((mu P) + (mu Q))%R = (mu (fun st : state => P st \/ Q st)).
Axiom positive : forall (mu : Measure) (P : Assertion), (mu P >= 0)%R.

(* --------Properties of Measures that follow from the axioms------------ *)
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

Theorem measure_inclusion_true: forall (mu: Measure) (P: Assertion), ((mu P) <= (mu True))%R.
Proof.
intros. apply measure_inclusion. intros. easy.
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

Theorem empty_measure_inclusion2: forall (mu:Measure) (P: Assertion), ((mu True) = 0)%R ->  ((mu P) = 0)%R.
Proof.
intros. assert (forall st : state, (P st) -> (assert_of_Prop True st)). intros. easy. pose proof measure_inclusion mu P (\{True\}) as H1.
pose proof H1 H0. rewrite -> H in H2. pose proof measure_leq0_implies_eq0 mu P. pose proof H3 H2. assumption.
Qed.

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

(* ------------------------------------------------------------------ *)

(* Defining interpretation of rigid real logic variables. *)

Definition Intp := total_map R.

(* Defining models to probabilistic state formulas *)
Definition Pstate := Measure * Intp.

(* Probabilistic state formulas as assertions *)

Inductive Pterm : Type :=
  | Preal (r : R)
  | Pvar (x : string)
  | Pint (A : Assertion)
  | Psum (p1 : Pterm) (p2 : Pterm)
  | Pmult (p1 : Pterm) (p2 : Pterm).

(* Function to evaluate Pterms.*)

Fixpoint Pteval (t : Pterm) (ps : Pstate): R := 
  match t with
    | Preal r => r
    | Pvar x => (snd ps) x
    | Pint A => (fst ps) A
    | Psum p1 p2 => (Pteval p1 ps) + (Pteval p2 ps)
    | Pmult p1 p2 => (Pteval p1 ps) * (Pteval p2 ps)
end.

(* Semantic definition of probabilistic state formula *)
Definition PAssertion : Type := Pstate -> Prop.


(* PAssertion Notation. *)

Definition PTermexp: Type :=  Pstate -> R.

Definition Passert_of_Prop (P : Prop) : PAssertion := fun _ => P.
Definition PTerm_of_R (r: R) : PTermexp := fun _=> r. 
Definition PTermexp_of_pterm (p: Pterm): PTermexp := fun ps => Pteval p ps. (* evaluate the term on the state *) 


Coercion Passert_of_Prop : Sortclass >-> PAssertion.
Coercion PTerm_of_R : R >->PTermexp.
Coercion PTermexp_of_pterm: Pterm >-> PTermexp.

Declare Custom Entry passn. (* The grammar for Hoare logic Assertions *)

Bind Scope passertion_scope with PAssertion.
Bind Scope passertion_scope with PTermexp.
Delimit Scope passertion_scope with passertion.
Open Scope passertion_scope.


Coercion Preal : R >-> Pterm.
Coercion Pvar : string >-> Pterm.
Coercion Pint : Assertion >-> Pterm. 
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
(* measure_sub_toss x r mu = [toss(x,r)]mu 
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
  (* Uniform Dice Roll Command *)
  | KRoll (x : string) (k : nat)
  (* End of Dice Roll Command *)
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

(* Uniform Dice Roll Notation *)
Notation " x 'roll' k " :=
          (KRoll x k)
              (in custom com at level 0, x constr at level 0,
             k constr at level 0, no associativity) : com_scope.
  (* End of Dice Roll Notation *)

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



Definition apply_func {A B: Type} (f: A->B) (x: A) := f x.


Fixpoint vector_sum {n: nat} (X: Vector.t R n) : R :=
  match X with
  | [] => 0%R
  | hd:: tl => (hd + vector_sum tl)%R 
end.

(* Function to generate the system of linear inequations of the While rules *)
Definition lin_ineq {n: nat} (i: nat) (X: Vector.t R n) (r2: Vector.t (Vector.t R n) n) (r1: Vector.t R n) : Prop :=
     Rge (List.nth i (Vector.to_list X) 0%R)  ((vector_sum (zip Rmult (List.nth i (Vector.to_list r2) (const 0%R n)) (X))) + (List.nth i (Vector.to_list r1) (0%R)))%R. 

Definition lin_ineq_lb {n: nat} (i: nat) (X: Vector.t R n) (r2: Vector.t (Vector.t R n) n) (r1: Vector.t R n) : Prop :=
     Rle (List.nth i (Vector.to_list X) 0%R)  ((vector_sum (zip Rmult (List.nth i (Vector.to_list r2) (const 0%R n)) (X))) + (List.nth i (Vector.to_list r1) (0%R)))%R.


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

(* another reformulation of antecedent_leq *)
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


Definition hoare_list_leq (hoare:  PAssertion -> Cmd -> PAssertion -> Prop) (s: Cmd)  
 (n: nat) (gammas: Vector.t Assertion n) (r2: Vector.t (Vector.t R n) n) (beta gamma: Assertion) (r1: Vector.t R n): Prop  := 
  Vector.fold_right and  (hoare_list hoare (Vector.map int_true_eq_one gammas) s (antecedent_leq gammas r2 beta gamma  r1)) True.  


Inductive dummy : PAssertion -> Cmd -> PAssertion -> Prop :=
  | all: forall P s Q, dummy P s Q. 

Check hoare_list_leq (fun P s Q => dummy P s Q).


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



(* Uniform Dice Roll Rule Helpers   *)

Fixpoint sum_R (f : nat -> R) (k : nat) : R :=
  match k with
  | 0 => 0
  | S n => f n + sum_R f n
  end.


Definition measure_sub_k (x: string) (k: nat) (P : Assertion) : Assertion :=
 fun st => ( P ((x !-> (Teval (Const k) st); (fst st)),(snd st))).

Fixpoint measure_sub_kroll_P (x: string) (k : nat) (mu : Measure) (P : Assertion) : R :=
match k with
| 0 => (mu (measure_sub_k x k P))
| S n =>  (measure_sub_kroll_P x n mu P) + (mu (measure_sub_k x k P))
end.


Definition measure_sub_kroll (x: string) (k : nat) (mu : Measure) : Measure :=
( fun P => ((1/(INR (k + 1))) * (measure_sub_kroll_P  x k mu P))%R). (* 0 to K *)

Definition kroll_pt (x : string) (k : nat) (eta : PAssertion) : PAssertion :=
  fun ps =>
    (eta (measure_sub_kroll x k (fst ps), snd ps)).

(* End of Dice Roll Helpers*)

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
  (* Dice Roll Rule *)
  | HKRoll : 
      forall (eta: PAssertion) (x : string) (k : nat), hoare_triple (kroll_pt x k eta) (KRoll x k) eta
  (* End of Dice Roll Rule *)
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
              (forall i : nat, (i < m) -> 
                    (hoare_triple (List.nth i (Vector.to_list (Vector.map int_true_eq_one G)) {{true}}) s (List.nth i (Vector.to_list (antecedent_leq G P beta gamma T)) {{true}}))
              )
      -> (forall (i:nat), (i < m) -> lin_ineq i X P T)
      -> (forall (i: nat) (y: string) (tempAssertion : Assertion) (tempR : R), 
              (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st <-> tempAssertion st) ->
              ((List.nth i (Vector.to_list X) 0%R) = tempR) ->
              hoare_triple {{((prob (beta /\ tempAssertion)) <= y) /\ ((prob (beta /\ tempAssertion)) = (prob true)) }}
                            <{ while beta do s end }>
                            {{(prob gamma) <= (tempR*y) }}
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
          )
      
      (* reformulation of while lb rule, more amenable to induction proofs *)
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
          )
    (* another reformulation of while lb rule to facilitate easier proofs. *)
    | HWhileLB3 : forall (m : nat) (beta : bexp) (gamma: Assertion) (s : Cmd) (G : Vector.t Assertion m) (X : Vector.t R m) (P : Vector.t (Vector.t R m) m) (T : Vector.t R m),
              (forall (i : nat), (i < m) -> (forall st, (List.nth i (Vector.to_list G) {{true}}) st -> Beval beta st))
                -> (forall (i j : nat), (i < m) -> (j < i) -> (forall st, ~ (((List.nth i (Vector.to_list G) {{true}}) st) /\ ((List.nth j (Vector.to_list G) {{true}}) st))))
                -> (forall (i : nat), (i < m) -> ((List.nth i (Vector.to_list T) 0%R) > 0)%R \/ exists (j : nat), (m > j) /\ (j > i) /\ ((List.nth j (Vector.to_list (List.nth i (Vector.to_list P) (const 0%R m))) 0%R) > 0)%R)
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
          )
. 


(* notation for Hoare triples *)

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P ->> Q" := (PAImplies P Q) 
        (in custom passn at level 96, left associativity, P custom passn, Q custom passn) : hoare_spec_scope.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q)
    (at level 2, P custom passn at level 99, c custom com at level 99, Q custom passn at level 99)
    : hoare_spec_scope.


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


Theorem RigidUnchanged: forall (y: string) (c: Cmd) (r: R), {{ y = r }} c {{ y = r}}.
Proof.
intros. apply HFree.
unfold is_analytical. intros. split. simpl. rewrite -> H. easy. simpl. rewrite -> H. easy.
Qed.

Theorem measure_false_is_zero: forall (mu: Measure), ((mu ({{false}})) = 0)%R.
Proof.
intros. pose proof measure_true_dest mu (\{ true \}).
        assert (((mu \{ ~ true \}) = 0)%R). lra.
        assert  (mu \{ ~ true \} = mu ({{ false }})). apply equivalence. easy.
        rewrite <- H1. easy.
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

Theorem helper1: forall (P Q R : PAssertion), 
    {{(P /\ Q) /\ R}} = {{P /\ (Q /\ R)}}.
Proof. intros. apply functional_extensionality. intros. simpl. apply propositional_extensionality. easy.
Qed.
                      
Definition trivial_measure: Measure := (fun A : Assertion => 0%R).
Definition trivial_intp : Intp := (fun y : string => 0%R).
Definition trivial_pstate : Pstate := (trivial_measure, trivial_intp).
 (* -------------------------------------------------------------- *)

(* Small example proofs showcasing the rules *)

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




Theorem trivial : forall (P Q : Prop), (P = Q) -> (P <-> Q).
Proof. intros. split.
  - rewrite H. intros. apply H0.
  - rewrite H. auto.
Qed.



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

End PHL.

