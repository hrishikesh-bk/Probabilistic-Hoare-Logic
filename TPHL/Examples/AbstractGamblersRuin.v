(** Gambler's Ruin with an abstract-state presentation.

    The goal is fixed at 7. A win (probability 1/3) doubles the gold
    and adds a fair bonus of 0 or 1. A loss halves the gold, rounded
    down. At zero the body skips, so the loop continues forever.

    The upper bound uses four abstract regions; the lower bound uses
    three regions, omitting the absorbing ruin state.
    No initial values are required for either Boolean variable. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
Require Import PHL Examples.Lib Examples.PrAtoms Soundness.StateFacts.
Require Import Soundness.AssertionFacts Completeness.StructuralRules
  Completeness.Freshness.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module AbstractGamblersRuin.

Local Notation "'#(' x ')'" := (pconst x)
  (in custom tpf at level 0, x constr at level 200) : tphl_scope.

Definition g : DomProgramVar := dom_program_var "g".
Definition win : BoolProgramVar := bool_program_var "win".
Definition bonus : BoolProgramVar := bool_program_var "bonus".

Definition win_rate : R := 1 / 3.
Definition bonus_rate : R := 1 / 2.

Lemma win_rate_valid : coin_probability_valid win_rate.
Proof. unfold coin_probability_valid, win_rate; lra. Qed.

Lemma bonus_rate_valid : coin_probability_valid bonus_rate.
Proof. unfold coin_probability_valid, bonus_rate; lra. Qed.

Definition doubled_gold : Term := \{ #(2%nat) * g \}.
Definition bonus_gold : Term := \{ #(2%nat) * g + #(1%nat) \}.
Definition halved_gold : Term := \{ g div #(2%nat) \}.

Definition guard : CFormula := \{ g < #(7%nat) \}.
Definition can_bet : CFormula := \{ #(1%nat) <= g \}.

Definition winning_branch : Cmd :=
  <{ bonus toss bonus_rate;
     if bonus then g := bonus_gold else g := doubled_gold end }>.

Definition losing_branch : Cmd := <{ g := halved_gold }>.

Definition body : Cmd :=
  <{ if can_bet then
       win toss win_rate;
       if win then winning_branch else losing_branch end
     else skip end }>.

Definition loop : Cmd := CWhile guard body.

(** Predicates over natural-number gold amounts. *)
Definition region_R : CFormula := \{ g = #(0%nat) \}.
Definition region_A : CFormula := \{ g = #(1%nat) \}.
Definition region_B : CFormula := \{ #(2%nat) <= g /\ g < #(4%nat) \}.
Definition region_C : CFormula := \{ #(4%nat) <= g /\ g < #(7%nat) \}.
Definition target : CFormula := \{ #(7%nat) <= g \}.

(** The natural-number division primitive already implements floor. *)
Lemma halved_gold_eval (v : state) :
  term_eval halved_gold v = Nat.div (dom_program_values v g) 2.
Proof. reflexivity. Qed.

Lemma doubled_gold_eval (v : state) :
  term_eval doubled_gold v = (2 * dom_program_values v g)%nat.
Proof. reflexivity. Qed.

Lemma bonus_gold_eval (v : state) :
  term_eval bonus_gold v = (2 * dom_program_values v g + 1)%nat.
Proof. reflexivity. Qed.

Lemma half_floor (n : nat) :
  (2 * (n / 2) <= n < 2 * (n / 2) + 2)%nat.
Proof.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdecomp.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hremainder.
  lia.
Qed.

Lemma halved_gold_floor (v : state) :
  (2 * term_eval halved_gold v <= dom_program_values v g <
   2 * term_eval halved_gold v + 2)%nat.
Proof. rewrite halved_gold_eval; apply half_floor. Qed.

(** Evaluation and comparison of the new operation agree with the
    expression helpers used by the later probability proofs. *)
Example halved_gold_comparison : term_eqb halved_gold halved_gold = true.
Proof. reflexivity. Qed.

Lemma guard_spec (v : state) :
  satisfies v guard <-> (dom_program_values v g < 7)%nat.
Proof. change (Nat.ltb (dom_program_values v g) 7 = true <->
               (dom_program_values v g < 7)%nat).
  apply Nat.ltb_lt. Qed.

Lemma can_bet_spec (v : state) :
  satisfies v can_bet <-> (1 <= dom_program_values v g)%nat.
Proof. change (Nat.leb 1 (dom_program_values v g) = true <->
               (1 <= dom_program_values v g)%nat).
  apply Nat.leb_le. Qed.

Lemma region_R_spec (v : state) :
  satisfies v region_R <-> dom_program_values v g = 0%nat.
Proof. change (Nat.eqb (dom_program_values v g) 0 = true <->
               dom_program_values v g = 0%nat).
  apply Nat.eqb_eq. Qed.

Lemma region_A_spec (v : state) :
  satisfies v region_A <-> dom_program_values v g = 1%nat.
Proof. change (Nat.eqb (dom_program_values v g) 1 = true <->
               dom_program_values v g = 1%nat).
  apply Nat.eqb_eq. Qed.

Lemma region_B_spec (v : state) :
  satisfies v region_B <-> (2 <= dom_program_values v g < 4)%nat.
Proof.
  unfold region_B; rewrite satisfies_and.
  change ((Nat.leb 2 (dom_program_values v g) = true /\
           Nat.ltb (dom_program_values v g) 4 = true) <->
          (2 <= dom_program_values v g < 4)%nat).
  rewrite Nat.leb_le, Nat.ltb_lt; reflexivity.
Qed.

Lemma region_C_spec (v : state) :
  satisfies v region_C <-> (4 <= dom_program_values v g < 7)%nat.
Proof.
  unfold region_C; rewrite satisfies_and.
  change ((Nat.leb 4 (dom_program_values v g) = true /\
           Nat.ltb (dom_program_values v g) 7 = true) <->
          (4 <= dom_program_values v g < 7)%nat).
  rewrite Nat.leb_le, Nat.ltb_lt; reflexivity.
Qed.

Lemma target_spec (v : state) :
  satisfies v target <-> (7 <= dom_program_values v g)%nat.
Proof. change (Nat.leb 7 (dom_program_values v g) = true <->
               (7 <= dom_program_values v g)%nat).
  apply Nat.leb_le. Qed.

Lemma target_is_exit (v : state) :
  satisfies v target <-> satisfies v (c_not guard).
Proof. rewrite target_spec, satisfies_not, guard_spec; lia. Qed.

Lemma exit_disables_guard (v : state) :
  satisfies v target -> cformula_eval_bool guard v = false.
Proof.
  rewrite target_spec.
  change ((7 <= dom_program_values v g)%nat ->
          Nat.ltb (dom_program_values v g) 7 = false).
  intro H; apply Nat.ltb_ge; exact H.
Qed.

Lemma ruin_keeps_loop_and_skips_betting (v : state) :
  satisfies v region_R ->
  cformula_eval_bool guard v = true /\
  cformula_eval_bool can_bet v = false.
Proof.
  rewrite region_R_spec; intro H.
  change (Nat.ltb (dom_program_values v g) 7 = true /\
          Nat.leb 1 (dom_program_values v g) = false).
  rewrite H; split; reflexivity.
Qed.

(** Deterministic assignment outcomes: no bonus, bonus, and loss.
    The row at zero checks the terms only; the actual body skips there. *)
Definition branch_values (n : nat) : nat * nat * nat :=
  (2 * n, 2 * n + 1, n / 2)%nat.

Lemma branch_values_eval (v : state) :
  (term_eval doubled_gold v, term_eval bonus_gold v,
   term_eval halved_gold v) = branch_values (dom_program_values v g).
Proof. reflexivity. Qed.

Example branch_values_table :
  map branch_values (seq 0 7) =
  [(0, 1, 0); (2, 3, 0); (4, 5, 1); (6, 7, 1);
   (8, 9, 2); (10, 11, 2); (12, 13, 3)]%nat.
Proof. reflexivity. Qed.

Lemma loss_from_B (n : nat) : (2 <= n < 4)%nat -> Nat.div n 2 = 1%nat.
Proof. intro H; pose proof (half_floor n); lia. Qed.

Lemma loss_from_C (n : nat) :
  (4 <= n < 7)%nat -> (2 <= Nat.div n 2 < 4)%nat.
Proof. intro H; pose proof (half_floor n); lia. Qed.

Lemma win_from_B (n : nat) :
  (2 <= n < 4)%nat ->
  (4 <= 2 * n < 7)%nat /\ (4 <= 2 * n + 1 <= 7)%nat.
Proof. lia. Qed.

Lemma bonus_exit_from_B (n : nat) :
  (2 <= n < 4)%nat -> ((7 <= 2 * n + 1)%nat <-> n = 3%nat).
Proof. lia. Qed.

Lemma win_from_C (n : nat) :
  (4 <= n < 7)%nat -> (7 <= 2 * n)%nat /\ (7 <= 2 * n + 1)%nat.
Proof. lia. Qed.

(** * Loop-free probability calculations

    This conditional helper is derived using IF, AND, FREE, consequence,
    and elimination of fresh logic variables. It uses no semantic
    completeness theorem. The same body calculation will serve both bounds. *)
Lemma condition_pterm_fresh_iff (p : Pterm) beta y :
  prob_logic_var_occurs_pterm y (condition_pterm p beta) <->
  prob_logic_var_occurs_pterm y p.
Proof.
  induction p; cbn [condition_pterm prob_logic_var_occurs_pterm]; tauto.
Qed.

Lemma derive_if_probability (beta gamma : CFormula) (C1 C2 : Cmd)
    (t1 t2 : Pterm) y :
  (forall z, ~ prob_logic_var_occurs_pterm z t1) ->
  (forall z, ~ prob_logic_var_occurs_pterm z t2) ->
  (forall z, hoare_derivable (p_eq (PVar z) t1) C1
    (p_eq (PVar z) (PProb gamma))) ->
  (forall z, hoare_derivable (p_eq (PVar z) t2) C2
    (p_eq (PVar z) (PProb gamma))) ->
  hoare_derivable
    (p_eq (PVar y) (PAdd (condition_pterm t1 beta)
      (condition_pterm t2 (c_not beta))))
    (CIf beta C1 C2) (p_eq (PVar y) (PProb gamma)).
Proof.
  intros Hfresh1 Hfresh2 H1 H2.
  set (a := condition_pterm t1 beta).
  set (b := condition_pterm t2 (c_not beta)).
  assert (Ha : forall z, ~ prob_logic_var_occurs_pterm z a).
  { intro z; unfold a; rewrite condition_pterm_fresh_iff; apply Hfresh1. }
  assert (Hb : forall z, ~ prob_logic_var_occurs_pterm z b).
  { intro z; unfold b; rewrite condition_pterm_fresh_iff; apply Hfresh2. }
  set (u := fresh_prob_logic_var [y]).
  set (v := fresh_prob_logic_var [u;y]).
  assert (Hu : ~ In u [y]) by apply fresh_prob_logic_var_not_in.
  assert (Hv : ~ In v [u;y]) by apply fresh_prob_logic_var_not_in.
  cbn in Hu, Hv.
  assert (Huy : y <> u) by tauto.
  assert (Hvy : y <> v) by tauto.
  assert (Huv : u <> v) by tauto.
  set (frame := p_eq (PVar y) (PAdd (PVar u) (PVar v)) : PFormula).
  set (bindings := [(u,a);(v,b)]).
  assert (Hind : independent_bindings bindings).
  { split.
    - cbn [bindings map]; repeat constructor; cbn; intuition congruence.
    - intros z r w t Hz Ht; cbn [bindings] in Ht.
      destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Ha |].
      destruct Ht as [Ht | Ht]; [inversion Ht; subst w t; apply Hb | contradiction]. }
  assert (Hpost : forall z r, In (z,r) bindings ->
    ~ prob_logic_var_occurs_pformula z (p_eq (PVar y) (PProb gamma))).
  { intros z r Hz; cbn [bindings] in Hz.
    destruct Hz as [Hz | Hz]; [inversion Hz; subst z r |].
    - cbn; intuition congruence.
    - destruct Hz as [Hz | Hz]; [inversion Hz; subst z r | contradiction].
      cbn; intuition congruence. }
  assert (Hder : hoare_derivable (bindings_precondition bindings frame)
    (CIf beta C1 C2) (p_eq (PVar y) (PProb gamma))).
  { eapply derive_post with (post := p_and
      (p_eq (PAdd (PVar u) (PVar v)) (PProb gamma)) frame).
    - apply HAnd.
      + eapply derive_pre with (pre' := if_precondition
          (p_eq (PVar u) t1) (p_eq (PVar v) t2) beta).
        * intros ps Hps H; cbn [bindings bindings_precondition] in H.
          rewrite !psatisfies_and in H.
          unfold if_precondition; apply psatisfies_and; split.
          -- change (psatisfies ps (p_eq (PVar u) a)); tauto.
          -- change (psatisfies ps (p_eq (PVar v) b)); tauto.
        * apply derive_if_eq;
            [apply H1 | apply H2].
      + eapply derive_pre with (pre' := frame).
        * intros ps Hps H; cbn [bindings bindings_precondition] in H.
          rewrite !psatisfies_and in H; tauto.
        * apply HFree; unfold frame; cbn; tauto.
    - intros ps Hps H; apply psatisfies_and in H; destruct H as [Hsum Hframe].
      apply psatisfies_eq in Hsum; unfold frame in Hframe; apply psatisfies_eq in Hframe.
      apply psatisfies_eq; cbn [pterm_eval] in *; congruence. }
  pose proof (derive_eliminate_bindings bindings frame _ _ Hind Hpost Hder) as Hresult.
  assert (Heq : substitute_bindings bindings frame = p_eq (PVar y) (PAdd a b)).
  { unfold bindings, frame; cbn [substitute_bindings subst_prob_pformula p_eq p_and p_not subst_prob_pterm].
    repeat match goal with
    | |- context [prob_logic_var_eq_dec ?z ?w] =>
        destruct (prob_logic_var_eq_dec z w); cbn [subst_prob_pterm]
    end; try congruence;
    rewrite (subst_prob_pterm_fresh v b a (Ha v)); reflexivity. }
  rewrite Heq in Hresult; exact Hresult.
Qed.

Definition bonus_pre (q : CFormula) : Pterm :=
  PAdd (condition_pterm (PProb (subst_dom_cformula g bonus_gold q)) (fvar bonus))
       (condition_pterm (PProb (subst_dom_cformula g doubled_gold q)) (c_not (fvar bonus))).
Definition winning_pre (q : CFormula) : Pterm :=
  toss_pterm bonus bonus_rate (bonus_pre q).
Definition bet_pre (q : CFormula) : Pterm :=
  PAdd (condition_pterm (winning_pre q) (fvar win))
       (condition_pterm (PProb (subst_dom_cformula g halved_gold q)) (c_not (fvar win))).
Definition body_pre (q : CFormula) : Pterm :=
  PAdd (condition_pterm (toss_pterm win win_rate (bet_pre q)) can_bet)
       (condition_pterm (PProb q) (c_not can_bet)).

Lemma winning_pre_fresh q z : ~ prob_logic_var_occurs_pterm z (winning_pre q).
Proof. unfold winning_pre, bonus_pre; cbn; tauto. Qed.

Lemma bet_toss_pre_fresh q z :
  ~ prob_logic_var_occurs_pterm z (toss_pterm win win_rate (bet_pre q)).
Proof. unfold bet_pre, winning_pre, bonus_pre; cbn; tauto. Qed.

Lemma body_pre_fresh q z : ~ prob_logic_var_occurs_pterm z (body_pre q).
Proof. unfold body_pre, bet_pre, winning_pre, bonus_pre; cbn; tauto. Qed.

Lemma assignment_probability (q : CFormula) t y :
  hoare_derivable (p_eq (PVar y) (PProb (subst_dom_cformula g t q)))
    (CDomAssign g t) (p_eq (PVar y) (PProb q)).
Proof.
  change (hoare_derivable (subst_dom_pformula g t (p_eq (PVar y) (PProb q)))
    (CDomAssign g t) (p_eq (PVar y) (PProb q))).
  apply HDomAssign.
Qed.

Lemma winning_probability q y :
  hoare_derivable (p_eq (PVar y) (winning_pre q)) winning_branch
    (p_eq (PVar y) (PProb q)).
Proof.
  unfold winning_branch, winning_pre.
  apply HSeq with (eta2 := p_eq (PVar y) (bonus_pre q)).
  - change (hoare_derivable (toss_pformula bonus bonus_rate
      (p_eq (PVar y) (bonus_pre q))) (CBoolToss bonus bonus_rate)
      (p_eq (PVar y) (bonus_pre q))).
    apply HBoolToss; exact bonus_rate_valid.
  - unfold bonus_pre; apply derive_if_probability; try (intros; cbn; tauto);
      intro z; apply assignment_probability.
Qed.

Lemma bet_probability q y :
  hoare_derivable (p_eq (PVar y) (bet_pre q))
    (CIf (fvar win) winning_branch losing_branch)
    (p_eq (PVar y) (PProb q)).
Proof.
  unfold bet_pre; apply derive_if_probability.
  - apply winning_pre_fresh.
  - intros; cbn; tauto.
  - apply winning_probability.
  - intro z; apply assignment_probability.
Qed.

Lemma body_probability q y :
  hoare_derivable (p_eq (PVar y) (body_pre q)) body
    (p_eq (PVar y) (PProb q)).
Proof.
  unfold body, body_pre; apply derive_if_probability.
  - apply bet_toss_pre_fresh.
  - intros; cbn; tauto.
  - intro z; apply HSeq with (eta2 := p_eq (PVar z) (bet_pre q)).
    + change (hoare_derivable (toss_pformula win win_rate
        (p_eq (PVar z) (bet_pre q))) (CBoolToss win win_rate)
        (p_eq (PVar z) (bet_pre q))).
      apply HBoolToss; exact win_rate_valid.
    + apply bet_probability.
  - intro z; apply HSkip.
Qed.

(** A concentration fact used on arbitrary admissible distributions, not
    just point masses. *)
Lemma supported_probability_zero (ps : Pstate) region q :
  pstate_admissible ps -> Pr[ps] region = Pr[ps] c_true ->
  (forall v, satisfies v region -> ~ satisfies v q) -> Pr[ps] q = 0.
Proof.
  intros Hps Hregion Hout.
  assert (Hd : forall v, ~ (satisfies v q /\ satisfies v region)).
  { intros v [Hq Hr]; exact (Hout v Hr Hq). }
  pose proof (Pr_disjoint ps Hps q region Hd).
  pose proof (Pr_le_true ps Hps (c_or q region)).
  pose proof (Pr_nonneg ps q); lra.
Qed.

(** * Upper transition bounds: zero-based order R, A, B, C *)
Definition upper_regions (i : nat) : CFormula :=
  match i with 0%nat => region_R | 1%nat => region_A
             | 2%nat => region_B | _ => region_C end.
Definition upper_transitions (i j : nat) : R :=
  match i, j with
  | 0%nat, 0%nat => 1
  | 1%nat, 0%nat | 2%nat, 1%nat | 3%nat, 2%nat => 2/3
  | 1%nat, 2%nat | 2%nat, 3%nat => 1/3
  | _, _ => 0
  end.
Definition upper_exits (i : nat) : R :=
  match i with 2%nat => 1/6 | 3%nat => 1/3 | _ => 0 end.
Definition upper_solution (i : nat) : R :=
  match i with 1%nat => 1/6 | 2%nat => 1/2 | 3%nat => 2/3 | _ => 0 end.
Definition exit_event : CFormula := c_and (c_not guard) c_true.

(** Arithmetic on gold is independent of both initial Boolean values. *)
Ltac gold_decide :=
  let v := fresh "v" in intros v;
  pose proof (half_floor (dom_program_values v g));
  unfold upper_regions, region_R, region_A, region_B, region_C, guard, can_bet,
    exit_event, doubled_gold, bonus_gold, halved_gold, t_div in *;
  cunfold; cdestruct;
  rewrite ?Nat.eqb_eq, ?Nat.eqb_neq, ?Nat.leb_le, ?Nat.leb_gt,
    ?Nat.ltb_lt, ?Nat.ltb_ge in *;
  intuition (try congruence; try lia).

(** Finite arithmetic checks inside a region do not refine the abstract
    chain: each probability premise still uses the entire region. *)
Ltac gold_supported_decide eval_spec :=
  let v := fresh "v" in let Hr := fresh "Hr" in
  intros v Hr; clear - v Hr; cbn [upper_regions] in Hr;
  rewrite ?region_R_spec, ?region_A_spec, ?region_B_spec, ?region_C_spec in Hr;
  let n := fresh "n" in let En := fresh "En" in
  remember (dom_program_values v g) as n eqn:En;
  let E := fresh "E" in
  assert (E : n = 0%nat \/ n = 1%nat \/ n = 2%nat \/ n = 3%nat \/
              n = 4%nat \/ n = 5%nat \/ n = 6%nat) by lia;
  destruct E as [E | [E | [E | [E | [E | [E | E]]]]]];
  rewrite E in *; clear E n;
  try solve [exfalso; clear - Hr; lia];
  apply eval_spec;
  unfold can_bet, c_and, c_not, c_true, c_le, c_lt, c_eq,
    tvar, tnat, t_add, t_mul, g in *;
  cbn [cformula_eval_bool term_eval dom_rel_eval dom_op_eval
    nat_domain nat_rel_eval nat_op_eval];
  rewrite <- En; reflexivity.

Ltac gold_supported_out := gold_supported_decide cformula_eval_bool_false.
Ltac gold_supported_in := gold_supported_decide cformula_eval_bool_spec.

(** Wrap each residual mass after supplying its interval [0,1],
    so the arithmetic tactic does not repeatedly visit it. *)
Definition event_mass (ps : Pstate) (q : CFormula) : R := Pr[ps] q.

Ltac bound_body_pre :=
  intros ps Hps Hregion Hunit;
  unfold body_pre, bet_pre, winning_pre, bonus_pre,
    upper_regions, region_R, region_A, region_B, region_C, exit_event, guard,
    bonus_gold, doubled_gold, halved_gold, t_div;
  ptrans; cbn [pterm_eval];
  let reg := lazymatch type of Hregion with
    | Pr[ps] ?reg = _ => reg end in
  repeat match goal with
  | |- context [Pr[ps] ?q] =>
      first [let Hz := fresh "Hz" in
        assert (Hz : Pr[ps] q = 0) by
          (apply (supported_probability_zero ps reg q Hps Hregion); gold_supported_out);
        rewrite Hz; clear Hz
      | let Hlo := fresh "Hlo" in let Hhi := fresh "Hhi" in
        pose proof (Pr_nonneg ps q) as Hlo;
        pose proof (Pr_le_true ps Hps q) as Hhi;
        change (0 <= event_mass ps q) in Hlo;
        change (event_mass ps q <= Pr[ps] c_true) in Hhi;
        change (Pr[ps] q) with (event_mass ps q)]
  end;
  unfold win_rate, bonus_rate, upper_transitions, upper_exits; lra.

Lemma upper_transition_pre i j : (i < 4)%nat -> (j < 4)%nat ->
  forall ps : Pstate, pstate_admissible ps ->
  Pr[ps] (upper_regions i) = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
  pterm_eval (body_pre (upper_regions j)) ps <= upper_transitions i j.
Proof.
  intros Hi Hj.
  assert (Ei : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
  assert (Ej : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
  destruct Ei as [-> | [-> | [-> | ->]]];
    destruct Ej as [-> | [-> | [-> | ->]]]; bound_body_pre.
Qed.

Lemma upper_exit_pre i : (i < 4)%nat ->
  forall ps : Pstate, pstate_admissible ps ->
  Pr[ps] (upper_regions i) = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
  pterm_eval (body_pre exit_event) ps <= upper_exits i.
Proof.
  intro Hi.
  assert (Ei : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
  destruct Ei as [-> | [-> | [-> | ->]]]; bound_body_pre.
Qed.

(** Eliminate a fresh variable holding the input probability calculation.
    The hypothesis quantifies over every supported unit distribution. *)
Lemma body_upper_from_pre region q r :
  (forall ps : Pstate, pstate_admissible ps ->
    Pr[ps] region = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
    pterm_eval (body_pre q) ps <= r) ->
  hoare_derivable (p_concentrated_unit region) body
    (PFLe (PProb q) (PConst r)).
Proof.
  intro Hbound.
  apply HConseqLeft with (pre' := PFLe (body_pre q) (PConst r)).
  - intros ps Hps H; unfold p_concentrated_unit in H.
    rewrite psatisfies_and, psatisfies_almost_sure, psatisfies_eq in H.
    apply psatisfies_le; cbn [pterm_eval] in *; apply Hbound; tauto.
  - set (z := prob_logic_var "_body").
    change (hoare_derivable
      (subst_prob_pformula z (body_pre q) (PFLe (PVar z) (PConst r)))
      body (PFLe (PProb q) (PConst r))).
    apply HElimv.
    + apply HConseqRight with (post := p_and
        (p_eq (PVar z) (PProb q)) (PFLe (PVar z) (PConst r))).
      * pvalid; split_hyps; lra.
      * apply HAnd.
        -- eapply HConseqLeft; [|apply body_probability].
           pvalid; tauto.
        -- eapply HConseqLeft; [|apply HFree; cbn; tauto].
           pvalid; tauto.
    + apply body_pre_fresh.
    + cbn; tauto.
Qed.

Lemma upper_body i : (i < 4)%nat ->
  hoare_derivable (p_concentrated_unit (upper_regions i)) body
    (while_body_post_upper 4 upper_regions (upper_transitions i)
      guard c_true (upper_exits i)).
Proof.
  intro Hi; unfold while_body_post_upper.
  cbn [finite_p_and]; repeat apply HAnd.
  - apply derive_true.
  - apply body_upper_from_pre; apply upper_transition_pre; lia.
  - apply body_upper_from_pre; apply upper_transition_pre; lia.
  - apply body_upper_from_pre; apply upper_transition_pre; lia.
  - apply body_upper_from_pre; apply upper_transition_pre; lia.
  - apply body_upper_from_pre; apply upper_exit_pre; lia.
Qed.

Lemma upper_regions_cover : while_regions_cover 4 guard upper_regions.
Proof.
  unfold while_regions_cover, cformula_valid.
  cbn [finite_c_or upper_regions]; gold_decide.
Qed.

(** Entrywise bounds need not form a stochastic row: at B the row and
    exit bounds sum to 7/6. The rule only needs the following inequalities. *)
Lemma upper_solution_valid :
  while_upper_solution 4 upper_solution upper_transitions upper_exits.
Proof.
  unfold while_upper_solution; below_cases;
    cbn [finite_r_sum upper_solution upper_transitions upper_exits];
    repeat split; lra.
Qed.

Notation y := (prob_logic_var "y").

Theorem abstract_gamblers_ruin_upper_y :
  hoare_derivable
    {{ box region_A /\ (prob true) <= y }} loop
    {{ (prob true) <= #(1/6) * y }}.
Proof.
  apply HConseqLeft with
    (pre' := {{ box (guard /\ region_A) /\ (prob true) <= y }}).
  - pvalid; split_hyps.
    rewrite (Pr_ext ps (c_and guard region_A) region_A) by gold_decide.
    split; assumption.
  - apply (HWhileUpper 4 1 guard c_true body upper_regions
      upper_solution upper_exits upper_transitions y).
    + lia.
    + apply upper_regions_cover.
    + apply upper_body.
    + apply upper_solution_valid.
Qed.

Theorem abstract_gamblers_ruin_upper :
  hoare_derivable
    {{ box region_A /\ (prob true) = 1 }} loop
    {{ (prob true) <= #(1/6) }}.
Proof.
  apply HConseq with
    (eta1 := subst_prob_pformula y (PConst 1)
      {{ box region_A /\ (prob true) <= y }})
    (eta2 := subst_prob_pformula y (PConst 1)
      {{ (prob true) <= #(1/6) * y }}).
  - ptrans; pvalid; split_hyps; split; lra.
  - apply HInstantiate; apply abstract_gamblers_ruin_upper_y.
  - ptrans; pvalid; lra.
Qed.


(** * Lower transition bounds: zero-based order C, B, A

    Ruin is omitted. C can exit immediately; B can reach the earlier
    region C; A can reach the earlier region B. *)
Definition lower_regions (i : nat) : CFormula :=
  match i with 0%nat => region_C | 1%nat => region_B | _ => region_A end.
Definition lower_transitions (i j : nat) : R :=
  match i, j with
  | 0%nat, 1%nat | 1%nat, 2%nat => 2/3
  | 1%nat, 0%nat => 1/6
  | 2%nat, 1%nat => 1/3
  | _, _ => 0
  end.
Definition lower_exits (i : nat) : R :=
  match i with 0%nat => 1/3 | _ => 0 end.
Definition lower_solution (i : nat) : R :=
  match i with 0%nat => 7/18 | 1%nat => 1/12 | 2%nat => 1/36 | _ => 0 end.

Lemma supported_probability_one (ps : Pstate) region q :
  pstate_admissible ps -> Pr[ps] region = Pr[ps] c_true ->
  Pr[ps] c_true = 1 ->
  (forall v, satisfies v region -> satisfies v q) -> Pr[ps] q = 1.
Proof.
  intros Hps Hregion Hunit Hin.
  pose proof (Pr_mono ps Hps region q Hin).
  pose proof (Pr_le_true ps Hps q); lra.
Qed.

(** Reuse the exact loop-free calculation [body_pre]. Events forced by
    every valuation in the region have mass one; all other events have
    nonnegative mass. In B, only the no-bonus win is guaranteed to land
    in C, giving 1/6. No exit event is guaranteed throughout B. *)
Ltac lower_bound_body_pre :=
  intros ps Hps Hregion Hunit; cbn [lower_regions] in Hregion;
  unfold body_pre, bet_pre, winning_pre, bonus_pre,
    lower_regions, region_R, region_A, region_B, region_C, exit_event, guard,
    bonus_gold, doubled_gold, halved_gold, t_div;
  ptrans; cbn [pterm_eval];
  let reg := lazymatch type of Hregion with
    | Pr[ps] ?reg = _ => reg end in
  repeat match goal with
  | |- context [Pr[ps] ?q] =>
      first [let Hone := fresh "Hone" in
        assert (Hone : Pr[ps] q = 1) by
          (apply (supported_probability_one ps reg q Hps Hregion Hunit);
           gold_supported_in);
        rewrite Hone; clear Hone
      | let Hlo := fresh "Hlo" in
        pose proof (Pr_nonneg ps q) as Hlo;
        change (0 <= event_mass ps q) in Hlo;
        change (Pr[ps] q) with (event_mass ps q)]
  end;
  unfold win_rate, bonus_rate, lower_transitions, lower_exits; lra.

Lemma lower_transition_pre i j : (i < 3)%nat -> (j < 3)%nat ->
  forall ps : Pstate, pstate_admissible ps ->
  Pr[ps] (lower_regions i) = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
  lower_transitions i j <= pterm_eval (body_pre (lower_regions j)) ps.
Proof.
  intros Hi Hj.
  assert (Ei : i = 0%nat \/ i = 1%nat \/ i = 2%nat) by lia.
  assert (Ej : j = 0%nat \/ j = 1%nat \/ j = 2%nat) by lia.
  destruct Ei as [-> | [-> | ->]];
    destruct Ej as [-> | [-> | ->]]; lower_bound_body_pre.
Qed.

Lemma lower_exit_pre i : (i < 3)%nat ->
  forall ps : Pstate, pstate_admissible ps ->
  Pr[ps] (lower_regions i) = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
  lower_exits i <= pterm_eval (body_pre exit_event) ps.
Proof.
  intro Hi.
  assert (Ei : i = 0%nat \/ i = 1%nat \/ i = 2%nat) by lia.
  destruct Ei as [-> | [-> | ->]]; lower_bound_body_pre.
Qed.

Lemma body_lower_from_pre region q r :
  (forall ps : Pstate, pstate_admissible ps ->
    Pr[ps] region = Pr[ps] c_true -> Pr[ps] c_true = 1 ->
    r <= pterm_eval (body_pre q) ps) ->
  hoare_derivable (p_concentrated_unit region) body
    (PFLe (PConst r) (PProb q)).
Proof.
  intro Hbound.
  apply HConseqLeft with (pre' := PFLe (PConst r) (body_pre q)).
  - intros ps Hps H; unfold p_concentrated_unit in H.
    rewrite psatisfies_and, psatisfies_almost_sure, psatisfies_eq in H.
    apply psatisfies_le; cbn [pterm_eval] in *; apply Hbound; tauto.
  - set (z := prob_logic_var "_body").
    change (hoare_derivable
      (subst_prob_pformula z (body_pre q) (PFLe (PConst r) (PVar z)))
      body (PFLe (PConst r) (PProb q))).
    apply HElimv.
    + apply HConseqRight with (post := p_and
        (p_eq (PVar z) (PProb q)) (PFLe (PConst r) (PVar z))).
      * pvalid; split_hyps; lra.
      * apply HAnd.
        -- eapply HConseqLeft; [|apply body_probability].
           pvalid; tauto.
        -- eapply HConseqLeft; [|apply HFree; cbn; tauto].
           pvalid; tauto.
    + apply body_pre_fresh.
    + cbn; tauto.
Qed.

Lemma lower_body i : (i < 3)%nat ->
  hoare_derivable (p_concentrated_unit (lower_regions i)) body
    (while_body_post_lower 3 lower_regions (lower_transitions i)
      guard c_true (lower_exits i)).
Proof.
  intro Hi; unfold while_body_post_lower.
  cbn [finite_p_and]; repeat apply HAnd.
  - apply derive_true.
  - apply body_lower_from_pre; apply lower_transition_pre; lia.
  - apply body_lower_from_pre; apply lower_transition_pre; lia.
  - apply body_lower_from_pre; apply lower_transition_pre; lia.
  - apply body_lower_from_pre; apply lower_exit_pre; lia.
Qed.

Lemma lower_regions_in_guard : while_regions_in_guard 3 guard lower_regions.
Proof.
  unfold while_regions_in_guard, cformula_valid; below_cases;
    cbn [lower_regions]; gold_decide.
Qed.

Lemma lower_regions_disjoint : while_regions_disjoint 3 lower_regions.
Proof.
  unfold while_regions_disjoint, cformula_valid.
  intros i j Hi Hj.
  assert (Ei : i = 1%nat \/ i = 2%nat) by lia.
  destruct Ei as [-> | ->].
  - assert (j = 0%nat) by lia; subst j; cbn [lower_regions]; gold_decide.
  - assert (Ej : j = 0%nat \/ j = 1%nat) by lia.
    destruct Ej as [-> | ->]; cbn [lower_regions]; gold_decide.
Qed.

Lemma lower_progress : while_progress 3 lower_transitions lower_exits.
Proof.
  unfold while_progress; below_cases.
  - left; cbn [lower_exits]; lra.
  - right; exists 0%nat; split; [lia | cbn [lower_transitions]; lra].
  - right; exists 1%nat; split; [lia | cbn [lower_transitions]; lra].
Qed.

(** In the upper ordering (R,A,B,C), the first row is the exact ruin
    row: probability 1 to itself, 0 to all other regions, and 0 to exit.
    A self-loop cannot satisfy the lower rule's progress requirement:
    index 0 has no earlier region and no positive direct exit. *)
Lemma ruin_first_fails_progress :
  ~ while_progress 4 upper_transitions upper_exits.
Proof.
  intro Hprogress; specialize (Hprogress 0%nat ltac:(lia)).
  destruct Hprogress as [Hexit | [j [Hj Htransition]]].
  - cbn [upper_exits] in Hexit; lra.
  - lia.
Qed.

Lemma lower_solution_valid :
  while_lower_solution 3 lower_solution lower_transitions lower_exits.
Proof.
  unfold while_lower_solution; below_cases;
    cbn [finite_r_sum lower_solution lower_transitions lower_exits];
    repeat split; lra.
Qed.

Theorem abstract_gamblers_ruin_lower_y :
  hoare_derivable
    {{ box region_A /\ y <= (prob true) }} loop
    {{ #(1/36) * y <= (prob true) }}.
Proof.
  apply HConseqLeft with
    (pre' := {{ box (guard /\ region_A) /\ y <= (prob true) }}).
  - pvalid; split_hyps.
    rewrite (Pr_ext ps (c_and guard region_A) region_A) by gold_decide.
    split; assumption.
  - apply (HWhileLower 3 2 guard c_true body lower_regions
      lower_solution lower_exits lower_transitions y).
    + lia.
    + apply lower_regions_in_guard.
    + apply lower_regions_disjoint.
    + apply lower_progress.
    + apply lower_body.
    + apply lower_solution_valid.
Qed.

Theorem abstract_gamblers_ruin_lower :
  hoare_derivable
    {{ box region_A /\ (prob true) = 1 }} loop
    {{ #(1/36) <= (prob true) }}.
Proof.
  apply HConseq with
    (eta1 := subst_prob_pformula y (PConst 1)
      {{ box region_A /\ y <= (prob true) }})
    (eta2 := subst_prob_pformula y (PConst 1)
      {{ #(1/36) * y <= (prob true) }}).
  - ptrans; pvalid; split_hyps; split; lra.
  - apply HInstantiate; apply abstract_gamblers_ruin_lower_y.
  - ptrans; pvalid; lra.
Qed.

Theorem abstract_gamblers_ruin_bounds :
  hoare_derivable
    {{ box region_A /\ (prob true) = 1 }} loop
    {{ #(1/36) <= (prob true) /\ (prob true) <= #(1/6) }}.
Proof.
  apply HAnd; [apply abstract_gamblers_ruin_lower | apply abstract_gamblers_ruin_upper].
Qed.

End AbstractGamblersRuin.
