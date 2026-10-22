(** Classical-layer facts: derived connectives, updates, and correctness of
    syntactic substitution on terms and classical formulas. *)
From Stdlib Require Import Reals Bool.Bool Lia FunctionalExtensionality.
From mathcomp Require boolp.
Require Import PHL.

Section StateFacts.
Context {D : Domain}.
Implicit Types (v : state D) (gamma beta : CFormula D) (t u : Term D).

Lemma satisfies_true v : satisfies v c_true.
Proof. cbn. tauto. Qed.

Lemma satisfies_not v gamma : satisfies v (c_not gamma) <-> ~ satisfies v gamma.
Proof. reflexivity. Qed.

(** Classical formulas are decidable, so the derived connectives have their
    usual meaning without appeal to excluded middle on arbitrary Props. *)
Lemma satisfies_dec v gamma : satisfies v gamma \/ ~ satisfies v gamma.
Proof.
  destruct (cformula_eval_bool gamma v) eqn:H.
  - left; apply cformula_eval_bool_spec; exact H.
  - right; apply cformula_eval_bool_false; exact H.
Qed.

Lemma satisfies_and v gamma1 gamma2 :
  satisfies v (c_and gamma1 gamma2) <-> satisfies v gamma1 /\ satisfies v gamma2.
Proof.
  cbn. destruct (satisfies_dec v gamma1), (satisfies_dec v gamma2); tauto.
Qed.

Lemma satisfies_or v gamma1 gamma2 :
  satisfies v (c_or gamma1 gamma2) <-> satisfies v gamma1 \/ satisfies v gamma2.
Proof.
  cbn. destruct (satisfies_dec v gamma1); tauto.
Qed.

Lemma satisfies_finite_c_or v m (formulas : nat -> CFormula D) :
  satisfies v (finite_c_or m formulas) <-> exists j, (j < m)%nat /\ satisfies v (formulas j).
Proof.
  induction m as [|m IH]; cbn [finite_c_or].
  - split; [contradiction | intros [j [Hj _]]; inversion Hj].
  - rewrite satisfies_or, IH. split.
    + intros [[j [Hj H]] | H].
      * exists j; split; [lia | exact H].
      * exists m; split; [lia | exact H].
    + intros [j [Hj H]]. destruct (PeanoNat.Nat.eq_dec j m) as [->|Hne]; [right; exact H|].
      left; exists j; split; [lia | exact H].
Qed.

Lemma formula_assertion_ext gamma1 gamma2 :
  (forall v, satisfies v gamma1 <-> satisfies v gamma2) ->
  formula_assertion gamma1 = formula_assertion gamma2.
Proof.
  intros H; apply functional_extensionality; intro v; apply boolp.propext; apply H.
Qed.

(** ** Updates *)

Lemma term_eval_update_bool t v b z : term_eval t (update_bool v b z) = term_eval t v.
Proof. induction t; cbn; congruence. Qed.

Lemma subst_dom_term_correct x t u v :
  term_eval (subst_dom_term x t u) v = term_eval u (update_dom v x (term_eval t v)).
Proof.
  induction u as [x'|y|c|o u1 IH1 u2 IH2]; cbn.
  - destruct (dom_program_var_eq_dec x' x); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

Lemma subst_dom_cformula_correct x t gamma v :
  satisfies v (subst_dom_cformula x t gamma) <->
  satisfies (update_dom v x (term_eval t v)) gamma.
Proof.
  induction gamma; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite !subst_dom_term_correct; reflexivity.
  - reflexivity.
  - rewrite IHgamma1, IHgamma2; reflexivity.
Qed.

Lemma subst_bool_cformula_correct b beta gamma v :
  satisfies v (subst_bool_cformula b beta gamma) <->
  satisfies (update_bool v b (cformula_eval_bool beta v)) gamma.
Proof.
  induction gamma as [b'|b'|r t1 t2| |g1 IH1 g2 IH2]; cbn.
  - destruct (bool_program_var_eq_dec b' b).
    + rewrite cformula_eval_bool_spec; reflexivity.
    + reflexivity.
  - reflexivity.
  - rewrite !term_eval_update_bool; reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

(** Substituting a Boolean constant, as in tossed formulas. *)
Lemma subst_bool_const_correct b gamma v (z : bool) :
  satisfies v (subst_bool_cformula b (if z then c_true else FFalse) gamma) <->
  satisfies (update_bool v b z) gamma.
Proof.
  rewrite subst_bool_cformula_correct. destruct z; reflexivity.
Qed.

End StateFacts.
