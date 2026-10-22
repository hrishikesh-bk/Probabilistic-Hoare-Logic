(** Fresh probabilistic logic variables and properties of probabilistic
    substitution.  Adapted from CPHL's Completeness/Freshness.v. *)
From Stdlib Require Import List String Ascii Arith Lia FunctionalExtensionality.
Require Import PHL Soundness.AssertionFacts.
Import ListNotations.

Section Freshness.
Context {D : Domain}.
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).

Fixpoint pterm_prob_vars (p : Pterm) : list ProbLogicVar :=
  match p with
  | PVar y => [y]
  | PConst _ | PProb _ => []
  | PAdd p1 p2 | PMul p1 p2 => pterm_prob_vars p1 ++ pterm_prob_vars p2
  end.

Fixpoint pformula_prob_vars (eta : PFormula) : list ProbLogicVar :=
  match eta with
  | PFLe p1 p2 => pterm_prob_vars p1 ++ pterm_prob_vars p2
  | PFFalse => []
  | PFImpl eta1 eta2 => pformula_prob_vars eta1 ++ pformula_prob_vars eta2
  end.

Lemma pterm_prob_vars_spec y p :
  In y (pterm_prob_vars p) <-> prob_logic_var_occurs_pterm y p.
Proof.
  induction p; cbn; try rewrite in_app_iff, IHp1, IHp2; intuition congruence.
Qed.

Lemma pformula_prob_vars_spec y eta :
  In y (pformula_prob_vars eta) <-> prob_logic_var_occurs_pformula y eta.
Proof.
  induction eta; cbn.
  - rewrite in_app_iff, !pterm_prob_vars_spec; reflexivity.
  - tauto.
  - rewrite in_app_iff, IHeta1, IHeta2; reflexivity.
Qed.

End Freshness.

(** A name made of more underscores than any avoided name is fresh. *)
Fixpoint repeated_underscores (n : nat) : string :=
  match n with
  | O => EmptyString
  | S n' => String "_"%char (repeated_underscores n')
  end.

Lemma repeated_underscores_length n : String.length (repeated_underscores n) = n.
Proof. induction n; cbn; congruence. Qed.

Definition prob_logic_var_name (y : ProbLogicVar) : string :=
  match y with prob_logic_var name => name end.

Fixpoint maximum_prob_logic_var_name_length (avoid : list ProbLogicVar) : nat :=
  match avoid with
  | [] => 0
  | y :: ys => Nat.max (String.length (prob_logic_var_name y))
      (maximum_prob_logic_var_name_length ys)
  end.

Definition fresh_prob_logic_var (avoid : list ProbLogicVar) : ProbLogicVar :=
  prob_logic_var (repeated_underscores (S (maximum_prob_logic_var_name_length avoid))).

Lemma prob_logic_var_name_length_bound y avoid : In y avoid ->
  (String.length (prob_logic_var_name y) <= maximum_prob_logic_var_name_length avoid)%nat.
Proof.
  induction avoid as [|z zs IH]; cbn; intros H; [contradiction |].
  destruct H as [<- | H]; [apply Nat.le_max_l |].
  eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_prob_logic_var_not_in avoid : ~ In (fresh_prob_logic_var avoid) avoid.
Proof.
  intro H; pose proof (prob_logic_var_name_length_bound _ _ H) as Hb.
  unfold fresh_prob_logic_var in Hb; cbn in Hb.
  rewrite repeated_underscores_length in Hb; lia.
Qed.

Section Substitution.
Context {D : Domain}.
Local Notation Pterm := (Pterm D).
Local Notation PFormula := (PFormula D).

Lemma subst_prob_pterm_fresh y r (p : Pterm) :
  ~ prob_logic_var_occurs_pterm y p -> subst_prob_pterm y r p = p.
Proof.
  induction p; cbn; intros H; try reflexivity.
  - destruct (prob_logic_var_eq_dec y0 y); [subst; exfalso; apply H; reflexivity | reflexivity].
  - rewrite IHp1, IHp2 by tauto; reflexivity.
  - rewrite IHp1, IHp2 by tauto; reflexivity.
Qed.

Lemma subst_prob_pformula_fresh y r (eta : PFormula) :
  ~ prob_logic_var_occurs_pformula y eta -> subst_prob_pformula y r eta = eta.
Proof.
  induction eta; cbn; intros H; try reflexivity.
  - rewrite !subst_prob_pterm_fresh by tauto; reflexivity.
  - rewrite IHeta1, IHeta2 by tauto; reflexivity.
Qed.

Lemma subst_prob_pterm_occurs_bound y replacement (p : Pterm) z :
  prob_logic_var_occurs_pterm z (subst_prob_pterm y replacement p) ->
  (z <> y /\ prob_logic_var_occurs_pterm z p) \/
  prob_logic_var_occurs_pterm z replacement.
Proof.
  induction p as [v | r | q | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; cbn.
  - destruct (prob_logic_var_eq_dec v y) as [Heq | Hneq]; cbn; intuition congruence.
  - tauto.
  - tauto.
  - intuition.
  - intuition.
Qed.

Lemma subst_prob_pformula_occurs_bound y replacement (eta : PFormula) z :
  prob_logic_var_occurs_pformula z (subst_prob_pformula y replacement eta) ->
  (z <> y /\ prob_logic_var_occurs_pformula z eta) \/
  prob_logic_var_occurs_pterm z replacement.
Proof.
  induction eta; cbn.
  - pose proof (subst_prob_pterm_occurs_bound y replacement p1 z).
    pose proof (subst_prob_pterm_occurs_bound y replacement p2 z); tauto.
  - tauto.
  - tauto.
Qed.

Lemma update_prob_here rho y r : update_prob rho y r y = r.
Proof. unfold update_prob. destruct (prob_logic_var_eq_dec y y); congruence. Qed.

Lemma update_prob_other rho y r z : z <> y -> update_prob rho y r z = rho z.
Proof. unfold update_prob. destruct (prob_logic_var_eq_dec z y); congruence. Qed.

End Substitution.
