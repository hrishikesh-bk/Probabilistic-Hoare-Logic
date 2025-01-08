Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import List.
Require Import Coq.Vectors.Vector. 
Require Import Coq.Reals.Reals.
Import ListNotations. 
Import VectorNotations.  

Open Scope R_scope.

Fixpoint fin_list (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n' => Fin.F1 :: List.map Fin.FS (fin_list n')
  end.


(* The number of memory variables [m] *)
Variable m : nat.

(* Memory variables for real and boolean registers *)
Inductive xM_var : Type := xMvar : Fin.t m -> xM_var.
Inductive bM_var : Type := bMvar : Fin.t m -> bM_var.

(* Logical variables *)
Inductive B_var : Type := Bvar : nat -> B_var.  (* Boolean logical variables *)
Inductive X_var : Type := Xvar : nat -> X_var.  (* Real logical variables *)
Inductive y_var : Type := yvar : nat -> y_var.  (* Probability logical variables *)

(* Equality decision functions for variables *)
Definition xM_var_eq_dec : forall (x1 x2 : xM_var), {x1 = x2} + {x1 <> x2}.
Proof.
  decide equality.
  apply Fin.eq_dec.
Defined.

Definition bM_var_eq_dec : forall (b1 b2 : bM_var), {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
  apply Fin.eq_dec.
Defined.

Definition B_var_eq_dec : forall (B1 B2 : B_var), {B1 = B2} + {B1 <> B2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Definition X_var_eq_dec : forall (X1 X2 : X_var), {X1 = X2} + {X1 <> X2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

Definition y_var_eq_dec : forall (y1 y2 : y_var), {y1 = y2} + {y1 <> y2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

(* Boolean equality functions *)
Definition xM_var_eqb (x1 x2 : xM_var) : bool :=
  if xM_var_eq_dec x1 x2 then true else false.

Definition bM_var_eqb (b1 b2 : bM_var) : bool :=
  if bM_var_eq_dec b1 b2 then true else false.

Definition B_var_eqb (B1 B2 : B_var) : bool :=
  if B_var_eq_dec B1 B2 then true else false.

Definition X_var_eqb (X1 X2 : X_var) : bool :=
  if X_var_eq_dec X1 X2 then true else false.

Definition y_var_eqb (y1 y2 : y_var) : bool :=
  if y_var_eq_dec y1 y2 then true else false.

(* EEPL syntax *)

(* Real terms *)
Inductive real_term : Type :=
  | rt_xm : xM_var -> real_term                         (* Memory variable xm *)
  | rt_X : X_var -> real_term                           (* Logical variable X *)
  | rt_c : R -> real_term                               (* Constant c from D *)
  | rt_plus : real_term -> real_term -> real_term       (* Addition t + t *)
  | rt_mult : real_term -> real_term -> real_term.      (* Multiplication t * t *)

(* Classical state formulas *)
Inductive class_state_formula : Type :=
  | csf_bm : bM_var -> class_state_formula                             (* Memory variable bm *)
  | csf_B : B_var -> class_state_formula                               (* Logical variable B *)
  | csf_leq : real_term -> real_term -> class_state_formula            (* Comparison t ≤ t *)
  | csf_ff : class_state_formula                                       (* False formula ff *)
  | csf_implies : class_state_formula -> class_state_formula -> class_state_formula.  (* Implication γ ⇒ γ *)

(* Probability terms *)
Inductive prob_term : Type :=
  | pt_y : y_var -> prob_term                                          (* Logical variable y *)
  | pt_r : R                                               (* Constant r from R *)
  | pt_measure : class_state_formula -> prob_term                      (* Measure term ∫ γ *)
  | pt_plus : prob_term -> prob_term -> prob_term                      (* Addition p + p *)
  | pt_mult : prob_term -> prob_term -> prob_term                      (* Multiplication p * p *)
  | pt_r_tilde : R -> prob_term.                                       (* Truncated constant r̃ *)

(* Probabilistic state formulas *)
Inductive prob_state_formula : Type :=
  | psf_leq : prob_term -> prob_term -> prob_state_formula             (* Comparison p ≤ p *)
  | psf_fff : prob_state_formula                                       (* False formula fff *)
  | psf_implies : prob_state_formula -> prob_state_formula -> prob_state_formula.  (* Implication η ⊃ η *)


(* Analytical Terms *)
Inductive analytical_term : Type :=
  | at_var : y_var -> analytical_term                          (* Variable x *)
  | at_const : R -> analytical_term                            (* Constant r *)
  | at_plus : analytical_term -> analytical_term -> analytical_term    (* a + a *)
  | at_mult : analytical_term -> analytical_term -> analytical_term    (* a * a *)
  | at_r_tilde : R -> analytical_term.                         (* Truncated constant r̃ *)

(* Analytical Formulas *)
Inductive analytical_formula : Type :=
  | af_leq : analytical_term -> analytical_term -> analytical_formula   (* a ≤ a *)
  | af_fff : analytical_formula                                         (* fff *)
  | af_implies : analytical_formula -> analytical_formula -> analytical_formula.  (* κ ⊃ κ *)
  


(* Basic Probabilistic Programming Language *)

Inductive cmd : Type :=
  | CSkip : cmd                                                 (* skip *)
  | CAssR : xM_var -> real_term -> cmd                          (* x_m ← t *)
  | CAssB : bM_var -> class_state_formula -> cmd                (* b_m ← γ *)
  | CToss : bM_var -> R -> cmd                                  (* toss(b_m, r) *)
  | CSeq : cmd -> cmd -> cmd                                    (* s; s *)
  | CIf : class_state_formula -> cmd -> cmd -> cmd              (* if γ then s else s *)
  | CWhile : class_state_formula -> cmd -> cmd.                 (* while γ do s *)

(* Tossed Terms and Tossed formulas Helpers*)
(* Function to replace bm with bool e in γ *)

Fixpoint replace_bm_in_gamma (bm : bM_var) (e : bool) (γ : class_state_formula) : class_state_formula :=
  match γ with
  | csf_bm bm' =>
      match bM_var_eq_dec bm bm' with
      | left _ => if e then csf_implies csf_ff csf_ff else csf_ff
      | right _ => csf_bm bm'
      end
  | csf_B B => csf_B B
  | csf_leq t1 t2 => csf_leq t1 t2
  | csf_ff => csf_ff
  | csf_implies γ1 γ2 => csf_implies (replace_bm_in_gamma bm e γ1) (replace_bm_in_gamma bm e γ2)
  end.

(* Tossed Terms toss(bm, r; p) *)
Fixpoint toss_p (bm : bM_var) (r : R) (p : prob_term) : prob_term :=
  match p with
  | pt_y y => pt_y y
  | pt_r r' => pt_r r'
  | pt_r_tilde r' => pt_r_tilde r'
  | pt_measure γ =>
      let γ_tt := replace_bm_in_gamma bm true γ in
      let γ_ff := replace_bm_in_gamma bm false γ in
      let term_tt := pt_measure γ_tt in
      let term_ff := pt_measure γ_ff in
      let r_tilde := pt_r_tilde r in
      let one_minus_r_tilde := pt_r_tilde (1 - r) in
      pt_plus (pt_mult r_tilde term_tt) (pt_mult one_minus_r_tilde term_ff)
  | pt_plus p1 p2 => pt_plus (toss_p bm r p1) (toss_p bm r p2)
  | pt_mult p1 p2 => pt_mult (toss_p bm r p1) (toss_p bm r p2)
  end.

(* Tossed formulas toss(bm, r; η) *)
Fixpoint toss_eta (bm : bM_var) (r : R) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (toss_p bm r p1) (toss_p bm r p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (toss_eta bm r η1) (toss_eta bm r η2)
  end.

(* Function to compute (p / γ) *)
Fixpoint cond_p (γ_cond : class_state_formula) (p : prob_term) : prob_term :=
  match p with
  | pt_y y => pt_y y
  | pt_r r => pt_r r
  | pt_r_tilde r => pt_r_tilde r
  | pt_measure γ => pt_measure (csf_implies γ_cond γ)
  | pt_plus p1 p2 => pt_plus (cond_p γ_cond p1) (cond_p γ_cond p2)
  | pt_mult p1 p2 => pt_mult (cond_p γ_cond p1) (cond_p γ_cond p2)
  end.

(* Function to compute (η / γ) *)
Fixpoint cond_eta (γ_cond : class_state_formula) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (cond_p γ_cond p1) (cond_p γ_cond p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (cond_eta γ_cond η1) (cond_eta γ_cond η2)
  end.

(* Substitution Functions*)

(* 1. Substitution Functions for Real Memory Variables *)

(* Substitute a real memory variable x_subst with a real term t_subst in a real term *)
Fixpoint subst_real_term (x_subst : xM_var) (t_subst : real_term) (t : real_term) : real_term :=
  match t with
  | rt_xm x =>
      if xM_var_eq_dec x_subst x then
        t_subst
      else
        rt_xm x
  | rt_X X => rt_X X
  | rt_c c => rt_c c
  | rt_plus t1 t2 => rt_plus (subst_real_term x_subst t_subst t1) (subst_real_term x_subst t_subst t2)
  | rt_mult t1 t2 => rt_mult (subst_real_term x_subst t_subst t1) (subst_real_term x_subst t_subst t2)
  end.

(* Substitute a real memory variable x_subst with a real term t_subst in a classical state formula *)
Fixpoint subst_class_state_formula_real (x_subst : xM_var) (t_subst : real_term) (γ : class_state_formula) : class_state_formula :=
  match γ with
  | csf_bm b => csf_bm b
  | csf_B B => csf_B B
  | csf_leq t1 t2 => csf_leq (subst_real_term x_subst t_subst t1) (subst_real_term x_subst t_subst t2)
  | csf_ff => csf_ff
  | csf_implies γ1 γ2 => csf_implies (subst_class_state_formula_real x_subst t_subst γ1) (subst_class_state_formula_real x_subst t_subst γ2)
  end.

(* Substitute a real memory variable x_subst with a real term t_subst in a probabilistic term *)
Fixpoint subst_prob_term_real (x_subst : xM_var) (t_subst : real_term) (p : prob_term) : prob_term :=
  match p with
  | pt_y y => pt_y y
  | pt_r r => pt_r r
  | pt_r_tilde r => pt_r_tilde r
  | pt_measure γ => pt_measure (subst_class_state_formula_real x_subst t_subst γ)
  | pt_plus p1 p2 => pt_plus (subst_prob_term_real x_subst t_subst p1) (subst_prob_term_real x_subst t_subst p2)
  | pt_mult p1 p2 => pt_mult (subst_prob_term_real x_subst t_subst p1) (subst_prob_term_real x_subst t_subst p2)
  end.

(* Substitute a real memory variable x_subst with a real term t_subst in a probabilistic state formula *)
Fixpoint subst_prob_state_formula_real (x_subst : xM_var) (t_subst : real_term) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (subst_prob_term_real x_subst t_subst p1) (subst_prob_term_real x_subst t_subst p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (subst_prob_state_formula_real x_subst t_subst η1) (subst_prob_state_formula_real x_subst t_subst η2)
  end.

(* 2. Substitution Functions for Boolean Memory Variables *)

(* Substitute a boolean memory variable b_subst with a formula γ_subst in a classical state formula *)
Fixpoint subst_class_state_formula_bool (b_subst : bM_var) (γ_subst : class_state_formula) (γ : class_state_formula) : class_state_formula :=
  match γ with
  | csf_bm b =>
      if bM_var_eq_dec b_subst b then
        γ_subst
      else
        csf_bm b
  | csf_B B => csf_B B
  | csf_leq t1 t2 => csf_leq t1 t2
  | csf_ff => csf_ff
  | csf_implies γ1 γ2 => csf_implies (subst_class_state_formula_bool b_subst γ_subst γ1) (subst_class_state_formula_bool b_subst γ_subst γ2)
  end.

(* Substitute a boolean memory variable b_subst with a formula γ_subst in a probabilistic term *)
Fixpoint subst_prob_term_bool (b_subst : bM_var) (γ_subst : class_state_formula) (p : prob_term) : prob_term :=
  match p with
  | pt_y y => pt_y y
  | pt_r r => pt_r r
  | pt_r_tilde r => pt_r_tilde r
  | pt_measure γ => pt_measure (subst_class_state_formula_bool b_subst γ_subst γ)
  | pt_plus p1 p2 => pt_plus (subst_prob_term_bool b_subst γ_subst p1) (subst_prob_term_bool b_subst γ_subst p2)
  | pt_mult p1 p2 => pt_mult (subst_prob_term_bool b_subst γ_subst p1) (subst_prob_term_bool b_subst γ_subst p2)
  end.

(* Substitute a boolean memory variable b_subst with a formula γ_subst in a probabilistic state formula *)
Fixpoint subst_prob_state_formula_bool (b_subst : bM_var) (γ_subst : class_state_formula) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (subst_prob_term_bool b_subst γ_subst p1) (subst_prob_term_bool b_subst γ_subst p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (subst_prob_state_formula_bool b_subst γ_subst η1) (subst_prob_state_formula_bool b_subst γ_subst η2)
  end.

(* Substitute a probabilistic variable y_subst with a probabilistic term p_subst in a probabilistic term *)
Fixpoint subst_prob_term_var (y_subst : y_var) (p_subst : prob_term) (p : prob_term) : prob_term :=
  match p with
  | pt_y y =>
      if y_var_eq_dec y_subst y then
        p_subst
      else
        pt_y y
  | pt_r r => pt_r r
  | pt_r_tilde r => pt_r_tilde r
  | pt_measure γ => pt_measure γ
  | pt_plus p1 p2 => pt_plus (subst_prob_term_var y_subst p_subst p1) (subst_prob_term_var y_subst p_subst p2)
  | pt_mult p1 p2 => pt_mult (subst_prob_term_var y_subst p_subst p1) (subst_prob_term_var y_subst p_subst p2)
  end.

(* Substitute a probabilistic variable y_subst with a probabilistic term p_subst in a probabilistic state formula *)
Fixpoint subst_prob_state_formula_var (y_subst : y_var) (p_subst : prob_term) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (subst_prob_term_var y_subst p_subst p1) (subst_prob_term_var y_subst p_subst p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (subst_prob_state_formula_var y_subst p_subst η1) (subst_prob_state_formula_var y_subst p_subst η2)
  end.

(* Hoare Logic Rules *)

(* Abbreviations for other operators *)
Definition psf_not (η : prob_state_formula) : prob_state_formula :=
  psf_implies η psf_fff.

Definition psf_true : prob_state_formula :=
  psf_implies psf_fff psf_fff.

Definition psf_and (η1 η2 : prob_state_formula) : prob_state_formula :=
  psf_not (psf_implies η1 (psf_not η2)).

Definition psf_or (η1 η2 : prob_state_formula) : prob_state_formula :=
  psf_implies (psf_not η1) η2.

Definition psf_eq (p1 p2 : prob_term) : prob_state_formula :=
  psf_and (psf_leq p1 p2) (psf_leq p2 p1).

Definition psf_geq (p1 p2 : prob_term) : prob_state_formula :=
  psf_leq p2 p1.

Definition psf_lt (p1 p2 : prob_term) : prob_state_formula :=
  psf_and (psf_leq p1 p2) (psf_not (psf_leq p2 p1)).

Definition psf_gt (p1 p2 : prob_term) : prob_state_formula :=
  psf_and (psf_leq p2 p1) (psf_not (psf_leq p1 p2)).

Definition csf_not (γ : class_state_formula) : class_state_formula :=
  csf_implies γ csf_ff.
  
Definition csf_true : class_state_formula :=
  csf_implies csf_ff csf_ff.

Definition csf_and (γ1 γ2 : class_state_formula) : class_state_formula :=
  csf_not (csf_implies γ1 (csf_not γ2)).

Definition csf_or (γ1 γ2 : class_state_formula) : class_state_formula :=
  csf_implies (csf_not γ1) γ2.

Definition csf_iff (γ1 γ2 : class_state_formula) : class_state_formula :=
  csf_and (csf_implies γ1 γ2) (csf_implies γ2 γ1).

Definition eta_perp (η1 η2 : prob_state_formula) (γ : class_state_formula) : prob_state_formula :=
  psf_and (cond_eta γ η1) (cond_eta (csf_not γ) η2).
  
(* Big conjunction *)
Definition csf_or_list (fs : list class_state_formula) : class_state_formula :=
  Coq.Lists.List.fold_right csf_or csf_ff fs.
  
(* Big disjunction *)
Definition csf_and_list (fs : list class_state_formula) : class_state_formula :=
  Coq.Lists.List.fold_right csf_and csf_true fs.

Definition psf_and_list (fs : list prob_state_formula) : prob_state_formula :=
  Coq.Lists.List.fold_right psf_and psf_true fs.

(* Collect probabilistic variables in a probabilistic term *)
Fixpoint pvar_p (p : prob_term) : list y_var :=
  match p with
  | pt_y y => [y]
  | pt_r _ => []
  | pt_r_tilde _ => []
  | pt_measure _ => []
  | pt_plus p1 p2 => pvar_p p1 ++ pvar_p p2
  | pt_mult p1 p2 => pvar_p p1 ++ pvar_p p2
  end.

(* Collect probabilistic variables in a probabilistic state formula *)
Fixpoint pvar_eta (η : prob_state_formula) : list y_var :=
  match η with
  | psf_leq p1 p2 => pvar_p p1 ++ pvar_p p2
  | psf_fff => []
  | psf_implies η1 η2 => pvar_eta η1 ++ pvar_eta η2
  end.

(* Check if a variable y does not occur in a list of variables *)
Definition not_in_list (y : y_var) (l : list y_var) : bool :=
  negb (List.existsb (fun y' => y_var_eqb y y') l).

(* Check if y ∉ PVar(p) *)
Definition not_in_pvar_p (y : y_var) (p : prob_term) : bool :=
  not_in_list y (pvar_p p).

(* Check if y ∉ PVar(η) *)
Definition not_in_pvar_eta (y : y_var) (η : prob_state_formula) : bool :=
  not_in_list y (pvar_eta η).

(* Check if a probabilistic term is analytical (contains no measure terms) *)
Fixpoint is_analytical_pterm (p : prob_term) : bool :=
  match p with
  | pt_y _ => true
  | pt_r _ => true
  | pt_r_tilde _ => true
  | pt_measure _ => false
  | pt_plus p1 p2 => is_analytical_pterm p1 && is_analytical_pterm p2
  | pt_mult p1 p2 => is_analytical_pterm p1 && is_analytical_pterm p2
  end.

(* Check if a probabilistic state formula is analytical *)
Fixpoint is_analytical (η : prob_state_formula) : bool :=
  match η with
  | psf_leq p1 p2 => is_analytical_pterm p1 && is_analytical_pterm p2
  | psf_fff => true
  | psf_implies η1 η2 => is_analytical η1 && is_analytical η2
  end.
  
(* function to compute sum over a vector of real numbers *)
Fixpoint sum_real_vector {n : nat} (v : Vector.t R n) : R := 
  match v with
  | [] => 0%R
  | h :: t => (h + sum_real_vector t)%R
  end.

(* function to compute dot product of two real vectors *)
Definition dot_product {n : nat} (v1 v2 : Vector.t R n) : R :=
  Vector.fold_left2 (fun acc x y => (acc + x * y)%R) 0%R v1 v2.
  
Axiom valid_psf: prob_state_formula -> Prop.
Axiom valid_csf: class_state_formula -> Prop.

 
(* Hoare logic rules *)
Inductive hoare_proof : prob_state_formula -> cmd -> prob_state_formula -> Prop :=
  (* Axiom [∫FREE] *)
  | H_IntegralFree : forall κ s,
      is_analytical κ = true ->
      hoare_proof κ s κ

  (* Axiom [SKIP] *)
  | H_Skip : forall η,
      hoare_proof η CSkip η

  (* Axiom [ASGR] *)
  | H_AssignR : forall η x t,
      let η_subst := subst_prob_state_formula_real x t η in
      hoare_proof η_subst (CAssR x t) η

  (* Axiom [ASGB] *)
  | H_AssignB : forall η b γ,
      let η_subst := subst_prob_state_formula_bool b γ η in
      hoare_proof η_subst  (CAssB b γ) η

  (* Axiom [TOSS] *)
  | H_Toss : forall η b r,
      let η_toss := toss_eta b r η in
      hoare_proof η_toss (CToss b r) η

  (* Rule [SEQ] *)
  | H_Seq : forall η0 η1 η2 s1 s2,
      hoare_proof η0 s1 η1 ->
      hoare_proof η1 s2 η2 ->
      hoare_proof η0 (CSeq s1 s2) η2

  (* Rule [IF] *)
  | H_If : forall η1 η2 γ s1 s2 y1 y2 γ0,
      hoare_proof η1 s1 (psf_eq (pt_y y1) (pt_measure γ0)) ->
      hoare_proof η2 s2 (psf_eq (pt_y y2) (pt_measure γ0)) ->
      let pre := eta_perp η1 η2 γ in
      let post := psf_eq (pt_plus (pt_y y1) (pt_y y2)) (pt_measure γ0) in
      hoare_proof pre (CIf γ s1 s2) post

  (* Rule [ELIMV] *)
  | H_ElimV : forall η1 η2 s y p,
      not_in_pvar_p y p = true ->
      not_in_pvar_eta y η2 = true ->
      let pre := psf_and η1 (psf_eq (pt_y y) p) in
      let η1_subst := subst_prob_state_formula_var y p η1 in
      hoare_proof pre s η2 ->
      hoare_proof η1_subst s η2

 (* Rule [CONS] *)
  | H_Cons : forall η0 η1 η2 η3 s,
    valid_psf (psf_implies η0 η1) ->
    hoare_proof η1 s η2 ->
    valid_psf (psf_implies η2 η3) ->
    hoare_proof η0 s η3

  (* Rule [OR] *)
  | H_Or : forall η0 η1 η2 s,
      hoare_proof η0 s η2 ->
      hoare_proof η1 s η2 ->
      hoare_proof (psf_or η0 η1) s η2

  (* Rule [AND] *)
  | H_And : forall η0 η1 η2 s,
      hoare_proof η0 s η1 ->
      hoare_proof η0 s η2 ->
      hoare_proof η0 s (psf_and η1 η2)
  (* Rule [WHILE_NOT] *)
  | H_While_Not : forall b γ s y,
      hoare_proof
        (psf_and
          (psf_eq (pt_measure (csf_and (csf_not b) γ)) (pt_y y))
          (psf_eq (pt_measure csf_true) (pt_y y)))
        (CWhile b s)
        (psf_and
          (psf_eq (pt_measure γ) (pt_y y))
          (psf_eq (pt_measure csf_true) (pt_y y)))
  (* Rule [WHILE^{UB}_{m,k}] *)
  | H_While_UB : forall (m : nat) (k : Fin.t m) (b : class_state_formula)
                       (gamma_list : Vector.t class_state_formula m)
                       (s : cmd) (x_list : Vector.t R m)
                       (r_list : Vector.t R m)
                       (r_matrix : Vector.t (Vector.t R m) m)
                       (y : y_var) (gamma : class_state_formula),
      (* Validity Condition *)
      valid_csf (csf_implies b (csf_or_list (Vector.to_list gamma_list))) ->
      (* Per-Iteration Effects *)
      (forall i : Fin.t m,
          hoare_proof
            (psf_and
              (psf_eq (pt_measure (Vector.nth gamma_list i)) (pt_measure csf_true))  
              (psf_eq (pt_measure (Vector.nth gamma_list i)) (pt_r 1%R)))             
            s
            (psf_and
              (psf_and_list
                (List.map (fun j => psf_leq (pt_measure (Vector.nth gamma_list j))
                                            (pt_r (Vector.nth (Vector.nth r_matrix i) j)))
                          (fin_list m)))
              (psf_leq (pt_measure (csf_and (csf_not b) gamma))
                       (pt_r (Vector.nth r_list i))))) ->
      (* System of Inequalities *)
      (forall i : Fin.t m,
          0%R <= Vector.nth x_list i <= 1%R /\
          Vector.nth x_list i >= (dot_product (Vector.nth r_matrix i) x_list + Vector.nth r_list i)%R) ->
      (* Conclusion *)
      hoare_proof
        (psf_and
          (psf_eq (pt_measure (csf_and b (Vector.nth gamma_list k))) (pt_measure csf_true)) 
          (psf_leq (pt_measure (csf_and b (Vector.nth gamma_list k))) (pt_y y)))
        (CWhile b s)
        (psf_leq (pt_measure gamma) (pt_mult (pt_r (Vector.nth x_list k)) (pt_y y)))

  (* Rule [WHILE^{LB}_{m,k}] *)
  | H_While_LB : forall (m : nat) (k : Fin.t m) (b : class_state_formula)
                       (gamma_list : Vector.t class_state_formula m)
                       (s : cmd) (x_list : Vector.t R m)
                       (r_list : Vector.t R m)
                       (r_matrix : Vector.t (Vector.t R m) m)
                       (y : y_var) (gamma : class_state_formula),
      (* Disjointness Condition *)
      (forall i j : Fin.t m, i <> j ->
          valid_csf (csf_iff (csf_and (Vector.nth gamma_list i) (Vector.nth gamma_list j)) csf_ff)) ->
      (* Invariant Under Loop Condition *)
      valid_csf (csf_and_list (Vector.to_list (Vector.map (fun γ_i => csf_implies γ_i b) gamma_list))) ->
      (* Per-Iteration Effects *)
      (forall i : Fin.t m,
          hoare_proof
            (psf_and
              (psf_eq (pt_measure (Vector.nth gamma_list i)) (pt_measure csf_true))  
              (psf_eq (pt_measure (Vector.nth gamma_list i)) (pt_r 1%R)))             
            s
            (psf_and
              (psf_and_list
                (List.map (fun j => psf_geq (pt_measure (Vector.nth gamma_list j))
                                            (pt_r (Vector.nth (Vector.nth r_matrix i) j)))
                          (fin_list m)))
              (psf_geq (pt_measure (csf_and (csf_not b) gamma))
                       (pt_r (Vector.nth r_list i))))) ->
      (* System of Inequalities *)
      (forall i : Fin.t m,
          ((Vector.nth r_list i > 0%R) \/
           exists j : Fin.t m, Nat.lt (proj1_sig (Fin.to_nat j)) (proj1_sig (Fin.to_nat i)) /\
                              Vector.nth (Vector.nth r_matrix i) j > 0%R) /\
          0%R <= Vector.nth x_list i <= 1%R /\
          Vector.nth x_list i <= (dot_product (Vector.nth r_matrix i) x_list + Vector.nth r_list i)%R) ->
      (* Conclusion *)
      hoare_proof
        (psf_and
          (psf_eq (pt_measure (csf_and b (Vector.nth gamma_list k))) (pt_measure csf_true))  
          (psf_geq (pt_measure (csf_and b (Vector.nth gamma_list k))) (pt_y y)))
        (CWhile b s)
        (psf_geq (pt_measure gamma) (pt_mult (pt_r (Vector.nth x_list k)) (pt_y y)))
  (* Rule [SUM] *)
  | H_Sum : forall η1 η2 γ1 γ2 s y1 y2 γ,
      hoare_proof (psf_and η1 (psf_eq (pt_measure γ1) (pt_measure csf_true))) s (psf_eq (pt_measure γ) (pt_y y1)) ->
      hoare_proof (psf_and η2 (psf_eq (pt_measure γ2) (pt_measure csf_true))) s (psf_eq (pt_measure γ) (pt_y y2)) ->
      valid_psf (psf_eq (pt_measure (csf_and γ1 γ2)) (pt_measure csf_ff)) ->
      let pre := psf_and (cond_eta γ1 η1)
                         (psf_and (cond_eta γ2 η2)
                                  (psf_eq (pt_measure (csf_or γ1 γ2)) (pt_measure csf_true))) in
      let post := psf_eq (pt_plus (pt_y y1) (pt_y y2)) (pt_measure γ) in
      hoare_proof pre s post.


(* Testing *)
Theorem test_hoare_proof : forall η,
  hoare_proof η CSkip η.
Proof.
  intros.
  apply H_Skip. Qed.

Theorem subst_test: forall bM: bM_var,
  subst_class_state_formula_bool bM (csf_bm bM) (csf_bm bM) = csf_bm bM.
Proof.
intros.
simpl.
destruct (bM_var_eq_dec bM bM).
- reflexivity.
- contradiction.
Qed.


Theorem subst_test_prob: forall bM: bM_var,
  subst_prob_state_formula_bool bM (csf_bm bM) 
  (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) 
   = (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) .
Proof.
intros.
unfold subst_prob_state_formula_bool.
unfold subst_prob_term_bool.
rewrite subst_test.
reflexivity.
(* simpl.
destruct (bM_var_eq_dec bM bM).
- simpl. reflexivity.
- contradiction. *)
Qed.


Theorem A: forall bM: bM_var,
hoare_proof
(subst_prob_state_formula_bool bM (csf_bm bM)
(psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true))) (CAssB bM (csf_bm bM))
(psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) -> 
hoare_proof (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) 
        (CAssB bM (csf_bm bM)) (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)).

Proof.
  intros.
  rewrite subst_test_prob in H.
  apply H.
  Qed.



Theorem assignb1_proof : forall bM: bM_var,
  hoare_proof (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) 
        (CAssB bM (csf_bm bM)) (psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)).
  Proof.
    intros.
    apply A.
    apply H_AssignB with (η:= psf_leq (pt_measure (csf_bm bM)) (pt_measure csf_true)) (b:= bM) (γ:= (csf_bm bM)). Qed. 

(* Axiom valid_psf: prob_state_formula -> Prop.
Axiom valid_csf: class_state_formula -> Prop. *)

  (* Axiom [TOSS]
  | H_Toss : forall η b r,
      let η_toss := toss_eta b r η in
      hoare_proof η_toss (CToss b r) η *)

(* Fixpoint toss_eta (bm : bM_var) (r : R) (η : prob_state_formula) : prob_state_formula :=
  match η with
  | psf_leq p1 p2 => psf_leq (toss_p bm r p1) (toss_p bm r p2)
  | psf_fff => psf_fff
  | psf_implies η1 η2 => psf_implies (toss_eta bm r η1) (toss_eta bm r η2)
  end. *)


Theorem B: forall bM: bM_var,
  (toss_eta bM 1 (psf_eq (pt_measure (csf_bm bM)) (pt_r 1))) = (psf_eq (pt_measure (csf_bm bM)) (pt_r 1)).
Proof.
  intros.
  simpl.
  unfold psf_eq.
  unfold toss_eta.
  unfold psf_and.


Theorem base_imp : forall bM: bM_var,
  hoare_proof (toss_eta bM 1 (psf_eq (pt_measure (csf_bm bM)) (pt_r 1))) 
                      (CToss bM 1) (psf_eq (pt_measure (csf_bm bM)) (pt_r 1)) ->
  hoare_proof   (psf_eq (pt_measure csf_true) (pt_r 1)) (CToss bM 1) (psf_eq (pt_measure (csf_bm bM)) (pt_r 1)).
Proof.
  intros.
  apply H_Toss.






Theorem base_toss : forall bM: bM_var, 
  hoare_proof   (psf_eq (pt_measure csf_true) (pt_r 1)) (CToss bM 1) (psf_eq (pt_measure (csf_bm bM)) (pt_r 1)).
Proof.
  apply H_Toss.


(* 
  Definition csf_not (γ : class_state_formula) : class_state_formula :=
  csf_implies γ csf_ff.
  
Definition csf_true : class_state_formula :=
  csf_implies csf_ff csf_ff. *)