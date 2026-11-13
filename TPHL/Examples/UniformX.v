(** A sampler for the escaping spline, built from fair coins, and the proof
    that it meets [SamplerSpec.sampler_spec].

    The sampler draws [val] uniformly from [{0, ..., x}] by rejection, with
    the bound [x] a program variable:

      val := x + 1;
      while (x + 1 <= val) do
        val := 0; ct := 0;
        while (ct <= x) do  b toss 1/2; val := 2 * val + b; ct := ct + 1  end
      end

    The inner loop draws [x + 1] fair bits, so [val] is uniform on
    [[0, 2^(x+1))]; the outer loop rejects [val > x].

    Proof outline, for [x = k] (only [HWhileLower] is used):
    - [body_step]: one inner iteration, derived rule by rule.
    - [inner_point]: the inner loop ends with [val = j] with probability at
      least [1/2^(k+1)], for each [j < 2^(k+1)], with the chain of regions
      "ct = k - i and val holds the first k - i bits of j".
    - [inner_range]: summing, [a <= val < a + n] with probability at least
      [n/2^(k+1)].
    - [outer_lb], [sampler_lb]: the outer loop is a one-region rejection
      loop; lower bounds for [val = 0], [val <> 0] and [x = k].
    - [sampler_correct]: postconditions hold over sub-probability states
      ([Pr(true) <= 1]), so lower bounds on disjoint events summing to 1
      are equalities. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat Setoid.
Require Import PHL Examples.Lib Examples.PrAtoms Examples.SamplerSpec Examples.EscapingSpline.
Require Import Soundness.StateFacts Soundness.AssertionFacts.
Require Import Completeness.StructuralRules.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

(** * Local helpers (as in [gamblersruin.v], [Uniform.v], [RandomWalk.v]) *)

Notation "'#(' x ')'" := (pconst x) (in custom tpf at level 0, x constr at level 200)
  : tphl_scope.

Definition Pc (ps : Pstate) (g : CFormula) : R := Pr[ps] g.

Ltac pcanon_one ps X Gs :=
  lazymatch Gs with
  | cons ?G ?rest =>
      first
        [ let E := fresh "E" in
          assert (E : Pr[ps] X = Pc ps G) by (unfold Pc; apply Pr_ext; cdecide);
          rewrite E in *; clear E
        | pcanon_one ps X rest ]
  | nil =>
      let E := fresh "E" in
      assert (E : Pr[ps] X = 0) by (rewrite <- (Pr_false ps); apply Pr_ext; cdecide);
      rewrite E in *; clear E
  end.

Ltac pcanon Gs :=
  repeat match goal with
  | |- context [Pr[?ps] ?X] => pcanon_one ps X Gs
  | H : context [Pr[?ps] ?X] |- _ => pcanon_one ps X Gs
  end.

Lemma Pr_conc_true (ps : Pstate) (h g : CFormula) : pstate_admissible ps ->
  Pr[ps] h = Pr[ps] c_true -> (forall v, satisfies v h -> satisfies v g) ->
  Pr[ps] g = Pr[ps] c_true.
Proof.
  intros Hps Hh Himp.
  pose proof (Pr_le_true ps Hps g). pose proof (Pr_mono ps Hps h g Himp). lra.
Qed.

Lemma Pr_conc_false (ps : Pstate) (h g : CFormula) : pstate_admissible ps ->
  Pr[ps] h = Pr[ps] c_true -> (forall v, satisfies v h -> ~ satisfies v g) -> Pr[ps] g = 0.
Proof.
  intros Hps Hh Himp.
  pose proof (Pr_split ps Hps c_true h) as Ht.
  replace (Pr[ps] (c_and c_true h)) with (Pr[ps] h) in Ht
    by (apply Pr_ext; intro v; rewrite satisfies_and; pose proof (satisfies_true v); tauto).
  pose proof (Pr_split ps Hps g h) as Hg.
  assert (E1 : Pr[ps] (c_and g h) <= 0).
  { rewrite <- (Pr_false ps). apply Pr_mono; [exact Hps|]. intros v Hv.
    rewrite satisfies_and in Hv. destruct Hv as [Hg' Hh']. apply (Himp v Hh' Hg'). }
  assert (E2 : Pr[ps] (c_and g (c_not h)) <= Pr[ps] (c_and c_true (c_not h))).
  { apply Pr_mono; [exact Hps|]. intros v Hv. rewrite !satisfies_and in *.
    split; [apply satisfies_true | tauto]. }
  pose proof (Pr_nonneg ps (c_and g h)). pose proof (Pr_nonneg ps (c_and g (c_not h))).
  lra.
Qed.

Ltac cdec :=
  let v := fresh "v" in let Hv := fresh "Hv" in
  intros v Hv; revert Hv; cunfold; cdestruct;
  rewrite ?PeanoNat.Nat.eqb_eq, ?PeanoNat.Nat.eqb_neq, ?PeanoNat.Nat.leb_le,
          ?PeanoNat.Nat.leb_gt, ?PeanoNat.Nat.ltb_lt, ?PeanoNat.Nat.ltb_ge in *;
  intuition (try congruence; try lia).

Ltac conc_rewrite ps Hps h Hh :=
  repeat match goal with
  | |- context [Pr[ps] ?g] =>
      lazymatch g with
      | c_true => fail
      | FImpl FFalse FFalse => fail
      | _ => first
               [ rewrite (Pr_conc_true ps h g Hps Hh) by cdec
               | rewrite (Pr_conc_false ps h g Hps Hh) by cdec ]
      end
  end.

Lemma derive_finite_p_and pre (c : Cmd) m (f : nat -> PFormula) :
  (forall j, (j < m)%nat -> hoare_derivable pre c (f j)) ->
  hoare_derivable pre c (finite_p_and m f).
Proof.
  induction m as [|m IH]; intros H; cbn [finite_p_and].
  - apply derive_true.
  - apply HAnd; [apply IH; intros j Hj; apply H; lia | apply H; lia].
Qed.

Lemma finite_r_sum_point m q (a : R) :
  finite_r_sum m (fun l => if Nat.eqb l q then a else 0) = if Nat.ltb q m then a else 0.
Proof.
  induction m as [|m IH]; cbn [finite_r_sum]; [destruct q; reflexivity|].
  rewrite IH. destruct (Nat.eqb_spec m q) as [->|Hne].
  - rewrite (proj2 (Nat.ltb_ge q q) (Nat.le_refl q)), (proj2 (Nat.ltb_lt q (S q)) ltac:(lia)).
    lra.
  - destruct (Nat.ltb_spec q m), (Nat.ltb_spec q (S m)); try lia; lra.
Qed.

Lemma finite_r_sum_zero m : finite_r_sum m (fun _ => 0) = 0.
Proof. induction m; cbn [finite_r_sum]; lra. Qed.

Lemma two_pow_pos k : 0 < 2 ^ k.
Proof. apply pow_lt; lra. Qed.

Module UniformX.

Notation x := (dom_program_var "x").
Notation val := (dom_program_var "val").
Notation ct := (dom_program_var "ct").
Notation b := (bool_program_var "b").
Notation y := (prob_logic_var "y").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").

Notation one := (tnat 1).
Notation two := (tnat 2).

(** * The program *)

Definition bit_if : Cmd :=
  <{ if b then val := two * val + one else val := two * val end }>.
Definition inner_body : Cmd := <{ b toss (1/2); bit_if; ct := ct + one }>.
Definition inner_guard : CFormula := \{ ct <= x \}.
Definition inner : Cmd := CWhile inner_guard inner_body.
Definition outer_body : Cmd := <{ val := #(0%nat); ct := #(0%nat); inner }>.
Definition outer_guard : CFormula := \{ x + one <= val \}.
Definition outer : Cmd := CWhile outer_guard outer_body.
Definition sampler : Cmd := CSeq (CDomAssign val \{ x + one \}) outer.

(** [cdecide] for goals with several symbolic atoms: split each atom by its
    specification; a case with inconsistent atoms is closed by [lia], the
    rest are propositional.  ([tauto] first is slow on the inconsistent
    cases, and [intuition (try lia)] calls [lia] at every leaf.) *)
Ltac cfast :=
  let v := fresh "v" in
  intro v; cunfold;
  repeat match goal with
  | |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c)
  | |- context [Nat.leb ?a ?c] => destruct (Nat.leb_spec a c)
  | |- context [Nat.ltb ?a ?c] => destruct (Nat.ltb_spec a c)
  end;
  assert (true = true) by reflexivity; assert (false = true -> False) by discriminate;
  first [ exfalso; lia | tauto ].

Lemma Pr_conc_and (ps : Pstate) (h g : CFormula) : pstate_admissible ps ->
  Pr[ps] h = Pr[ps] c_true -> Pr[ps] g = Pr[ps] (c_and g h).
Proof.
  intros Hps Hh. rewrite (Pr_split ps Hps g h).
  rewrite (Pr_conc_false ps h (c_and g (c_not h)) Hps Hh); [lra|].
  intros v Hv Hg. rewrite satisfies_and, satisfies_not in Hg. tauto.
Qed.

(** * The inner body, rule by rule *)

Lemma tt_iff : (true = true) <-> True.
Proof. tauto. Qed.
Lemma ft_iff : (false = true) <-> False.
Proof. split; [discriminate | tauto]. Qed.

(** Evaluating a closed propositional formula (only [True], [False],
    [->], [<->]) by rewriting; [tauto] is slow to refute such formulas. *)
Lemma imp_T_l (P : Prop) : (True -> P) <-> P.
Proof. tauto. Qed.
Lemma imp_F_l (P : Prop) : (False -> P) <-> True.
Proof. tauto. Qed.
Lemma imp_T_r (P : Prop) : (P -> True) <-> True.
Proof. tauto. Qed.
Lemma iff_T_l (P : Prop) : (True <-> P) <-> P.
Proof. tauto. Qed.
Lemma iff_T_r (P : Prop) : (P <-> True) <-> P.
Proof. tauto. Qed.
Lemma iff_F_l (P : Prop) : (False <-> P) <-> (P -> False).
Proof. tauto. Qed.
Lemma iff_F_r (P : Prop) : (P <-> False) <-> (P -> False).
Proof. tauto. Qed.

Ltac cleaf :=
  rewrite ?tt_iff, ?ft_iff;
  repeat first [ rewrite imp_T_l | rewrite imp_F_l | rewrite imp_T_r
               | rewrite iff_T_l | rewrite iff_T_r | rewrite iff_F_l | rewrite iff_F_r ];
  exact I.

Lemma eqb_2a1_2p a p : (2 * a + 1 =? 2 * p)%nat = false.
Proof. apply Nat.eqb_neq. lia. Qed.
Lemma eqb_2a_2p a p : (2 * a =? 2 * p)%nat = (a =? p)%nat.
Proof. destruct (Nat.eqb_spec a p), (Nat.eqb_spec (2 * a) (2 * p)); lia. Qed.
Lemma eqb_2a1_S2p a p : (2 * a + 1 =? S (2 * p))%nat = (a =? p)%nat.
Proof. destruct (Nat.eqb_spec a p), (Nat.eqb_spec (2 * a + 1) (S (2 * p))); lia. Qed.
Lemma eqb_2a_S2p a p : (2 * a =? S (2 * p))%nat = false.
Proof. apply Nat.eqb_neq. lia. Qed.
Lemma eqb_a1_Sc a c : (a + 1 =? S c)%nat = (a =? c)%nat.
Proof. destruct (Nat.eqb_spec a c), (Nat.eqb_spec (a + 1) (S c)); lia. Qed.

(** After rewriting the arithmetic atoms of one iteration
    ([2 val + 1 = 2p], [ct + 1 = S c], ...) into [val = p], [ct = c] or
    [false], no arithmetic is left: each case is a closed formula. *)
Ltac cfast3 :=
  let v := fresh "v" in
  intro v; cunfold;
  rewrite ?eqb_2a1_2p, ?eqb_2a_2p, ?eqb_2a1_S2p, ?eqb_2a_S2p, ?eqb_a1_Sc;
  cdestruct; cleaf.

Ltac pcanon_closed_one ps X Gs :=
  lazymatch Gs with
  | cons ?G ?rest =>
      first
        [ let E := fresh "E" in
          assert (E : Pr[ps] X = Pc ps G) by (unfold Pc; apply Pr_ext; cfast3);
          rewrite E in *; clear E
        | pcanon_closed_one ps X rest ]
  | nil =>
      let E := fresh "E" in
      assert (E : Pr[ps] X = 0) by (rewrite <- (Pr_false ps); apply Pr_ext; cfast3);
      rewrite E in *; clear E
  end.

Ltac pcanon_closed Gs :=
  repeat match goal with
  | |- context [Pr[?ps] ?X] => pcanon_closed_one ps X Gs
  | H : context [Pr[?ps] ?X] |- _ => pcanon_closed_one ps X Gs
  end.

(** With all mass on [h], replace every [Pr(g)] in the goal by [Pr(g /\ h)]. *)
Ltac conc_all ps Hps h Hh :=
  repeat match goal with
  | |- context [Pr[ps] ?g] =>
      lazymatch g with
      | c_and _ h => fail
      | _ => rewrite (Pr_conc_and ps h g Hps Hh)
      end
  end.

(** [bit_if] with an exact postcondition [r = Pr(g)]: IF= on the two
    assignments, then the branch variables [y1], [y2] instantiated by the
    branch masses [a1], [a2] (as [ifthen_0] in [EscapingSpline.v]). *)
Lemma bit_if_exact (pre : PFormula) (g : CFormula) (a1 a2 r : R) :
  a1 + a2 = r ->
  pformula_valid
    (PFImpl pre
       (subst_prob_pformula y1 (PConst a1) (subst_prob_pformula y2 (PConst a2)
          (if_precondition
             (subst_dom_pformula val \{ two * val + one \} {{ y1 = (prob g) }})
             (subst_dom_pformula val \{ two * val \} {{ y2 = (prob g) }})
             (FProgBool b))))) ->
  hoare_derivable pre bit_if {{ #(r) = (prob g) }}.
Proof.
  intros Hr Hpre.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst a1) (subst_prob_pformula y2 (PConst a2)
               (if_precondition
                  (subst_dom_pformula val \{ two * val + one \} {{ y1 = (prob g) }})
                  (subst_dom_pformula val \{ two * val \} {{ y2 = (prob g) }})
                  (FProgBool b))))
    (eta2 := subst_prob_pformula y1 (PConst a1) (subst_prob_pformula y2 (PConst a2)
               {{ y1 + y2 = (prob g) }})).
  - exact Hpre.
  - apply HInstantiate. apply HInstantiate. unfold bit_if.
    apply HIfEq; apply HDomAssign.
  - intros ps Hps H. apply psatisfies_eq in H. apply psatisfies_eq. cbn in *. lra.
Qed.

(** Side condition of a step of [body_step]: all mass on [h]. *)
Ltac body_side Gs :=
  ptrans; pvalid; split_hyps;
  match goal with
  | Hps : pstate_admissible ?ps, Hh : Pr[?ps] ?h = Pr[?ps] ?t |- _ =>
      lazymatch t with
      | c_true => idtac
      | FImpl FFalse FFalse => idtac
      end;
      conc_all ps Hps h Hh
  end;
  pcanon_closed Gs; unfold Pc in *; repeat split; lra.

(** One inner iteration from [x = k, ct = c, val = p]: the toss, the four
    facts after [bit_if] (one IF= each), and the counter. *)
Lemma body_step (k c p : nat) :
  hoare_derivable
    (p_concentrated_unit \{ x = k /\ ct = c /\ val = p \})
    inner_body
    {{ (prob (x = k /\ ct = #(S c))) = 1 /\ (prob true) = 1 /\
       (prob (x = k /\ ct = #(S c) /\ val = #((2 * p)%nat))) = #(1/2) /\
       (prob (x = k /\ ct = #(S c) /\ val = #(S (2 * p)))) = #(1/2) }}.
Proof.
  unfold inner_body.
  apply HSeq with
    (eta2 := {{ (prob ((x = k /\ ct = c /\ val = p) /\ b)) = #(1/2) /\
                (prob ((x = k /\ ct = c /\ val = p) /\ ~ b)) = #(1/2) /\
                (prob (x = k /\ ct = c /\ val = p)) = (prob true) /\ (prob true) = 1 }}).
  - apply HConseqLeft with
      (pre' := toss_pformula b (1/2)
                 {{ (prob ((x = k /\ ct = c /\ val = p) /\ b)) = #(1/2) /\
                    (prob ((x = k /\ ct = c /\ val = p) /\ ~ b)) = #(1/2) /\
                    (prob (x = k /\ ct = c /\ val = p)) = (prob true) /\ (prob true) = 1 }}).
    + ptrans; pvalid; split_hyps.
      pcanon_closed [\{ x = k /\ ct = c /\ val = p \}; \{ true \}].
      unfold Pc in *. repeat split; lra.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HSeq with
      (eta2 := {{ #(1/2) = (prob (x = k /\ ct = c /\ val = #((2 * p)%nat))) /\
                  #(1/2) = (prob (x = k /\ ct = c /\ val = #(S (2 * p)))) /\
                  #(1) = (prob (x = k /\ ct = c)) /\ #(1) = (prob true) }}).
    + apply HAnd; [|apply HAnd; [|apply HAnd]].
      * apply (bit_if_exact _ _ 0 (1/2)); [lra|].
        body_side
          [\{ (x = k /\ ct = c /\ val = p) /\ b \}; \{ (x = k /\ ct = c /\ val = p) /\ ~ b \};
           \{ x = k /\ ct = c /\ val = p \}; \{ true \}].
      * apply (bit_if_exact _ _ (1/2) 0); [lra|].
        body_side
          [\{ (x = k /\ ct = c /\ val = p) /\ b \}; \{ (x = k /\ ct = c /\ val = p) /\ ~ b \};
           \{ x = k /\ ct = c /\ val = p \}; \{ true \}].
      * apply (bit_if_exact _ _ (1/2) (1/2)); [lra|].
        body_side
          [\{ (x = k /\ ct = c /\ val = p) /\ b \}; \{ (x = k /\ ct = c /\ val = p) /\ ~ b \};
           \{ x = k /\ ct = c /\ val = p \}; \{ true \}].
      * apply (bit_if_exact _ _ (1/2) (1/2)); [lra|].
        body_side
          [\{ (x = k /\ ct = c /\ val = p) /\ b \}; \{ (x = k /\ ct = c /\ val = p) /\ ~ b \};
           \{ x = k /\ ct = c /\ val = p \}; \{ true \}].
    + apply HConseqLeft with
        (pre' := subst_dom_pformula ct \{ ct + one \}
                   {{ (prob (x = k /\ ct = #(S c))) = 1 /\ (prob true) = 1 /\
                      (prob (x = k /\ ct = #(S c) /\ val = #((2 * p)%nat))) = #(1/2) /\
                      (prob (x = k /\ ct = #(S c) /\ val = #(S (2 * p)))) = #(1/2) }}).
      * ptrans; pvalid; split_hyps.
        pcanon_closed [\{ x = k /\ ct = c /\ val = #((2 * p)%nat) \};
                     \{ x = k /\ ct = c /\ val = #(S (2 * p)) \};
                     \{ x = k /\ ct = c \}; \{ true \}].
        unfold Pc in *. repeat split; lra.
      * apply HDomAssign.
Qed.

Lemma finite_r_sum_ext m (f g : nat -> R) :
  (forall l, (l < m)%nat -> f l = g l) -> finite_r_sum m f = finite_r_sum m g.
Proof.
  induction m as [|m IH]; intros H; cbn [finite_r_sum]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H m) by lia. reflexivity.
Qed.

(** * The inner loop: [val = j] with probability [1/2^(k+1)] *)

Section Inner.
Variables (k j : nat).
Hypothesis Hj : (j < 2 ^ S k)%nat.

(** The first [k - i] bits of [j]. *)
Definition q (i : nat) : nat := j / 2 ^ S i.

Definition Rg (i : nat) : CFormula := \{ x = k /\ ct = #((k - i)%nat) /\ val = #(q i) \}.
Definition trans (i l : nat) : R := if Nat.eqb (S l) i then 1/2 else 0.
Definition exits (i : nat) : R := if Nat.eqb i 0 then 1/2 else 0.
Definition sol (i : nat) : R := 1 / 2 ^ S i.
Definition gam : CFormula := \{ x = k /\ val = j \}.

Lemma q_step i : (q i = q (S i) * 2 + (q i mod 2))%nat /\ (q i mod 2 < 2)%nat.
Proof.
  unfold q. split; [|apply Nat.mod_upper_bound; lia].
  rewrite (Nat.pow_succ_r' 2 (S i)), (Nat.mul_comm 2 (2 ^ S i)), <- Nat.Div0.div_div.
  pose proof (Nat.div_mod_eq (j / 2 ^ S i) 2). lia.
Qed.

Lemma j_step : (j = q 0 * 2 + (j mod 2))%nat /\ (j mod 2 < 2)%nat.
Proof.
  unfold q. cbn [Nat.pow]. rewrite Nat.mul_1_r. split; [|apply Nat.mod_upper_bound; lia].
  pose proof (Nat.div_mod_eq j 2). lia.
Qed.

Lemma q_top : q k = 0%nat.
Proof. unfold q. apply Nat.div_small. exact Hj. Qed.

(** The post-state of one iteration from region [i]: all mass at
    [ct = k - i + 1], split evenly between the two extensions of [q i]. *)
Definition step_post (i : nat) : PFormula :=
  {{ (prob (x = k /\ ct = #(S (k - i)))) = 1 /\ (prob true) = 1 /\
     (prob (x = k /\ ct = #(S (k - i)) /\ val = #((2 * q i)%nat))) = #(1/2) /\
     (prob (x = k /\ ct = #(S (k - i)) /\ val = #(S (2 * q i)))) = #(1/2) }}.

Lemma step_derivable i :
  hoare_derivable (p_concentrated_unit (Rg i)) inner_body (step_post i).
Proof. apply body_step. Qed.

Lemma step_facts i ps : (i < S k)%nat -> pstate_admissible ps -> psatisfies ps (step_post i) ->
  (forall l, (l < S k)%nat -> Pr[ps] (Rg l) = trans i l) /\
  Pr[ps] (c_and (c_not inner_guard) gam) = exits i.
Proof.
  intros Hi Hps H. unfold step_post in H.
  psimpl_in H. cbn [pterm_eval] in H. unfold pconst in H. cbn [pterm_eval] in H.
  destruct H as [Hh [Ht [HA HB]]].
  set (h := \{ x = k /\ ct = #(S (k - i)) \}) in *.
  assert (Hh' : Pr[ps] h = Pr[ps] c_true) by lra.
  split.
  - intros l Hl. rewrite (Pr_conc_and ps h (Rg l) Hps Hh'). unfold trans.
    destruct (Nat.eqb_spec (S l) i) as [<-|Hne].
    + destruct (q_step l) as [Hq Hm].
      unfold Rg, h. set (a := q (S l)) in *. set (r := q l) in *. clearbody a r.
      destruct (r mod 2) as [|[|]] eqn:E; [| |lia].
      * rewrite <- HA. apply Pr_ext. cfast.
      * rewrite <- HB. apply Pr_ext. cfast.
    + rewrite <- (Pr_false ps). apply Pr_ext. unfold Rg, h.
      set (a := q i) in *. set (r := q l) in *. clearbody a r. cfast.
  - rewrite (Pr_conc_and ps h _ Hps Hh'). unfold exits.
    destruct (Nat.eqb_spec i 0) as [->|Hne].
    + destruct j_step as [Hq Hm]. unfold inner_guard, gam, h.
      set (a := q 0) in *. clearbody a.
      destruct (j mod 2) as [|[|]] eqn:E; [| |lia].
      * rewrite <- HA. apply Pr_ext. cfast.
      * rewrite <- HB. apply Pr_ext. cfast.
    + rewrite <- (Pr_false ps). apply Pr_ext. unfold inner_guard, gam, h.
      set (a := q i) in *. clearbody a. cfast.
Qed.

Lemma sol_step i : 1 / 2 * sol i = sol (S i).
Proof. unfold sol. cbn [pow]. field. apply pow_nonzero. lra. Qed.

Lemma sol_bounds i : 0 <= sol i <= 1.
Proof.
  unfold sol. pose proof (pow_R1_Rle 2 (S i) ltac:(lra)).
  pose proof (two_pow_pos (S i)). split.
  - left. apply Rdiv_lt_0_compat; lra.
  - apply (Rmult_le_reg_r (2 ^ S i)); [lra|]. field_simplify; lra.
Qed.

(** [W^LB] with regions [Rg 0 .. Rg k], starting from [Rg k]
    ([ct = 0], [val = 0]). *)
Theorem inner_lb :
  hoare_derivable
    (p_and (p_almost_sure (c_and inner_guard (Rg k))) (PFLe (PVar y) (PProb c_true)))
    inner (PFLe (PMul (PConst (sol k)) (PVar y)) (PProb gam)).
Proof.
  apply (HWhileLower (S k) k inner_guard gam inner_body Rg sol exits trans y).
  - lia.
  - while_side. intros i Hi. unfold Rg, inner_guard. cfast.
  - while_side. intros i l Hi Hl. unfold Rg. cfast.
  - while_side. intros [|i] Hi; unfold exits, trans.
    + left. cbn. lra.
    + right. exists i. split; [lia|]. rewrite Nat.eqb_refl. lra.
  - intros i Hi. eapply HConseqRight; [|apply step_derivable].
    intros ps Hps H. destruct (step_facts i ps Hi Hps H) as [F1 F2].
    unfold while_body_post_lower. apply psatisfies_and. split.
    + apply finite_p_and_spec. intros l Hl. apply psatisfies_le. cbn [pterm_eval].
      rewrite F1 by exact Hl. lra.
    + apply psatisfies_le. cbn [pterm_eval]. rewrite F2. lra.
  - unfold while_lower_solution. intros i Hi. split; [|apply sol_bounds].
    destruct i as [|i]; unfold exits, trans.
    + rewrite (finite_r_sum_ext _ _ (fun _ => 0)) by (intros l _; cbn; lra).
      rewrite finite_r_sum_zero. unfold sol. cbn. lra.
    + rewrite (finite_r_sum_ext _ _ (fun l => if Nat.eqb l i then 1 / 2 * sol i else 0)).
      * rewrite finite_r_sum_point.
        destruct (Nat.ltb_spec i (S k)); [|lia]. rewrite sol_step. cbn. lra.
      * intros l _. cbn [Nat.eqb]. destruct (Nat.eqb_spec l i) as [->|]; lra.
Qed.

End Inner.

(** [conc_rewrite] with [cfast] for the implications. *)
Ltac conc_fast :=
  split_hyps;
  match goal with
  | Hps : pstate_admissible ?ps, Hh : Pr[?ps] ?h = Pr[?ps] ?t |- _ =>
      lazymatch t with
      | c_true => idtac
      | FImpl FFalse FFalse => idtac
      end;
      repeat match goal with
      | |- context [Pr[ps] ?g] =>
          lazymatch g with
          | c_true => fail
          | FImpl FFalse FFalse => fail
          | _ => first
                   [ rewrite (Pr_conc_true ps h g Hps Hh) by cfast
                   | rewrite (Pr_conc_false ps h g Hps Hh) by cfast ]
          end
      end;
      pose proof (Pr_true_le1 ps Hps)
  end.

(** Premise of an assignment or of [HInstantiate] whose pre- and
    postconditions say "all mass on ...". *)
Ltac conc_side :=
  unfold p_concentrated_unit, p_almost_sure in *; ptrans; pvalid;
  change (FImpl FFalse FFalse) with (@c_true nat_domain) in *;
  conc_fast; repeat split; lra.

Lemma Sk_le k : (S k <= 2 ^ S k)%nat.
Proof. pose proof (Nat.pow_gt_lin_r 2 (S k) ltac:(lia)); lia. Qed.

(** Start of the inner loop: all mass on [x = k, ct = 0, val = 0]. *)
Definition pre_in (k : nat) : PFormula :=
  p_concentrated_unit \{ x = k /\ ct = #(0%nat) /\ val = #(0%nat) \}.

Theorem inner_point k j : (j < 2 ^ S k)%nat ->
  hoare_derivable (pre_in k) inner
    (PFLe (PConst (1 / 2 ^ S k)) (PProb \{ x = k /\ val = j \})).
Proof.
  intros Hj.
  eapply HConseqRight; [|eapply HConseqLeft;
    [|apply (HInstantiate y 1 _ _ _ (inner_lb k j Hj))]].
  - unfold sol, gam. ptrans; pvalid. lra.
  - unfold pre_in, Rg. rewrite q_top by exact Hj. rewrite Nat.sub_diag.
    unfold inner_guard. conc_side.
Qed.

(** [val] in [[a, a + n)]. *)
Definition range (k a n : nat) : CFormula := \{ x = k /\ a <= val /\ val < #((a + n)%nat) \}.

Theorem inner_range k a n : (a + n <= 2 ^ S k)%nat ->
  hoare_derivable (pre_in k) inner
    (PFLe (PConst (INR n / 2 ^ S k)) (PProb (range k a n))).
Proof.
  induction n as [|n IH]; intros Han.
  - eapply HConseqRight; [|apply (inner_point k 0); pose proof (Sk_le k); lia].
    intros ps Hps _. apply psatisfies_le. cbn [pterm_eval INR].
    unfold Rdiv. rewrite Rmult_0_l. apply Pr_nonneg.
  - eapply HConseqRight;
      [|apply HAnd; [apply IH; lia | apply (inner_point k (a + n)); lia]].
    intros ps Hps H. apply psatisfies_and in H as [H1 H2].
    rewrite psatisfies_le in H1, H2. apply psatisfies_le. cbn [pterm_eval] in *.
    rewrite (Pr_split ps Hps (range k a (S n)) \{ val < #((a + n)%nat) \}).
    rewrite (Pr_ext ps (c_and (range k a (S n)) _) (range k a n)) by (unfold range; cfast).
    rewrite (Pr_ext ps (c_and (range k a (S n)) _) \{ x = k /\ val = #((a + n)%nat) \})
      by (unfold range; cfast).
    rewrite S_INR. unfold Rdiv in *. rewrite Rmult_plus_distr_r, Rmult_1_l.
    rewrite Rmult_1_l in H2. lra.
Qed.

(** * The outer loop: one region, [x = k] and rejected *)

Definition O (k : nat) : CFormula := \{ x = k /\ x + one <= val \}.
Definition rej (k : nat) : nat := (2 ^ S k - S k)%nat.

Theorem outer_body_lb k a n gamma : (a + n <= S k)%nat ->
  (forall v, satisfies v (range k a n) -> satisfies v (c_and (c_not outer_guard) gamma)) ->
  hoare_derivable (p_concentrated_unit (O k)) outer_body
    (while_body_post_lower 1 (fun _ => O k) (fun _ => INR (rej k) / 2 ^ S k)
       outer_guard gamma (INR n / 2 ^ S k)).
Proof.
  intros Han Himp. pose proof (Sk_le k) as Hle. unfold outer_body.
  apply HSeq with (eta2 := p_concentrated_unit \{ x = k /\ val = #(0%nat) \}).
  { apply HConseqLeft with
      (pre' := subst_dom_pformula val (tnat 0) (p_concentrated_unit \{ x = k /\ val = #(0%nat) \})).
    - unfold O. conc_side.
    - apply HDomAssign. }
  apply HSeq with (eta2 := pre_in k).
  { apply HConseqLeft with (pre' := subst_dom_pformula ct (tnat 0) (pre_in k)).
    - unfold pre_in. conc_side.
    - apply HDomAssign. }
  eapply HConseqRight;
    [|apply HAnd; [apply (inner_range k (S k) (rej k)) | apply (inner_range k a n)];
      unfold rej; lia].
  intros ps Hps H. apply psatisfies_and in H as [H1 H2].
  rewrite psatisfies_le in H1, H2. cbn [pterm_eval] in *.
  unfold while_body_post_lower. apply psatisfies_and. split.
  - apply finite_p_and_spec. intros l _. apply psatisfies_le. cbn [pterm_eval].
    eapply Rle_trans; [exact H1|]. apply Pr_mono; [exact Hps|].
    unfold range, O, rej. cfast.
  - apply psatisfies_le. cbn [pterm_eval].
    eapply Rle_trans; [exact H2|]. apply Pr_mono; [exact Hps|exact Himp].
Qed.

Theorem outer_lb k a n gamma : (0 < n)%nat -> (a + n <= S k)%nat ->
  (forall v, satisfies v (range k a n) -> satisfies v (c_and (c_not outer_guard) gamma)) ->
  hoare_derivable
    (p_and (p_almost_sure (c_and outer_guard (O k))) (PFLe (PVar y) (PProb c_true)))
    outer (PFLe (PMul (PConst (INR n / INR (S k))) (PVar y)) (PProb gamma)).
Proof.
  intros Hn Han Himp. pose proof (Sk_le k) as Hle.
  assert (HSk : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (Hnk : INR n <= INR (S k)) by (apply le_INR; lia).
  apply (HWhileLower 1 0 outer_guard gamma outer_body (fun _ => O k)
           (fun _ => INR n / INR (S k)) (fun _ => INR n / 2 ^ S k)
           (fun _ _ => INR (rej k) / 2 ^ S k) y).
  - lia.
  - while_side. below_cases. unfold O, outer_guard. cfast.
  - while_side. intros; lia.
  - while_side. below_cases. left.
    apply Rdiv_lt_0_compat; [apply lt_0_INR; lia | apply two_pow_pos].
  - below_cases. apply (outer_body_lb k a n gamma); assumption.
  - unfold while_lower_solution. below_cases. cbn [finite_r_sum]. split.
    + apply Req_le. unfold rej. rewrite minus_INR by exact Hle. rewrite pow_INR.
      replace (INR 2) with 2 by (cbn; lra). field.
      split; [apply pow_nonzero; lra | lra].
    + split.
      * apply Rmult_le_pos; [apply pos_INR | left; apply Rinv_0_lt_compat; lra].
      * apply (Rmult_le_reg_r (INR (S k))); [lra|]. unfold Rdiv.
        rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(** * The sampler *)

Theorem sampler_lb k a n gamma : (0 < n)%nat -> (a + n <= S k)%nat ->
  (forall v, satisfies v (range k a n) -> satisfies v (c_and (c_not outer_guard) gamma)) ->
  hoare_derivable (SamplerSpec.sampler_pre k) sampler
    (PFLe (PConst (INR n / INR (S k))) (PProb gamma)).
Proof.
  intros Hn Han Himp. unfold sampler.
  apply HSeq with (eta2 := p_concentrated_unit (c_and outer_guard (O k))).
  - apply HConseqLeft with
      (pre' := subst_dom_pformula val \{ x + one \} (p_concentrated_unit (c_and outer_guard (O k)))).
    2: apply HDomAssign.
    unfold SamplerSpec.sampler_pre, O, outer_guard. conc_side.
  - eapply HConseqRight; [|eapply HConseqLeft;
      [|apply (HInstantiate y 1 _ _ _ (outer_lb k a n gamma Hn Han Himp))]].
    + ptrans; pvalid. lra.
    + conc_side.
Qed.

Definition gz (k : nat) : CFormula := \{ x = k /\ val = #(0%nat) \}.
Definition gn (k : nat) : CFormula := \{ x = k /\ ~ (val = #(0%nat)) \}.

Lemma Pr_zn ps k : pstate_admissible ps -> Pr[ps] (gz k) + Pr[ps] (gn k) <= 1.
Proof.
  intros Hps.
  rewrite (Pr_ext ps (gz k) (c_and \{ x = k \} \{ val = #(0%nat) \})) by (unfold gz; cfast).
  rewrite (Pr_ext ps (gn k) (c_and \{ x = k \} (c_not \{ val = #(0%nat) \})))
    by (unfold gn; cfast).
  rewrite <- Pr_split by exact Hps.
  pose proof (Pr_le_true ps Hps \{ x = k \}). pose proof (Pr_true_le1 ps Hps). lra.
Qed.

Theorem sampler_zn k :
  hoare_derivable (SamplerSpec.sampler_pre k) sampler
    (p_and (PFLe (PConst (1 / INR (S k))) (PProb (gz k)))
           (PFLe (PConst (INR k / INR (S k))) (PProb (gn k)))).
Proof.
  assert (Hz : hoare_derivable (SamplerSpec.sampler_pre k) sampler
                 (PFLe (PConst (1 / INR (S k))) (PProb (gz k)))).
  { replace 1 with (INR 1) at 1 by reflexivity.
    apply (sampler_lb k 0 1); [lia | lia |]. unfold range, gz, outer_guard. cfast. }
  apply HAnd; [exact Hz|]. destruct k as [|k].
  - eapply HConseqRight; [|exact Hz]. intros ps Hps _. apply psatisfies_le.
    cbn [pterm_eval INR]. unfold Rdiv. rewrite Rmult_0_l. apply Pr_nonneg.
  - apply (sampler_lb (S k) 1 (S k)); [lia | lia |]. unfold range, gn, outer_guard. cfast.
Qed.

Theorem sampler_correct : SamplerSpec.sampler_spec sampler.
Proof.
  assert (Hk : forall k, 0 < INR k + 1) by (intros; pose proof (pos_INR k); lra).
  constructor; intros k.
  - eapply HConseqRight; [|apply (sampler_zn k)].
    intros ps Hps H. apply psatisfies_and in H as [H1 H2]. rewrite psatisfies_le in H1, H2.
    apply psatisfies_eq. cbn [pterm_eval] in *. pose proof (Pr_zn ps k Hps).
    unfold gz, gn in *. rewrite S_INR in *.
    assert (E : INR k / (INR k + 1) = 1 - 1 / (INR k + 1)) by (field; specialize (Hk k); lra).
    lra.
  - eapply HConseqRight; [|apply (sampler_zn k)].
    intros ps Hps H. apply psatisfies_and in H as [H1 H2]. rewrite psatisfies_le in H1, H2.
    apply psatisfies_eq. cbn [pterm_eval] in *. pose proof (Pr_zn ps k Hps).
    unfold gz, gn in *. rewrite S_INR in *.
    assert (E : INR k / (INR k + 1) = 1 - 1 / (INR k + 1)) by (field; specialize (Hk k); lra).
    lra.
  - eapply HConseqRight; [|apply (sampler_lb k 0 (S k) \{ x = k \}); [lia | lia |]].
    + ptrans; pvalid.
      unfold Rdiv in H. rewrite Rinv_r in H by (apply not_0_INR; lia).
      match goal with |- Pr[ps] ?g = _ => pose proof (Pr_le_true ps Hps g) end.
      pose proof (Pr_true_le1 ps Hps). lra.
    + unfold range, outer_guard. cfast.
Qed.

(** The escaping spline of [EscapingSpline.v] with this sampler. *)
Theorem escaping_spline_term (n : nat) : (n > 0)%nat ->
  hoare_derivable {{ (prob true) = 1 }} (EscapingSpline.Escaping_spline sampler)
    {{ #(1 - 1 / (INR n + 1)) <= (prob (x = #(0%nat))) }}.
Proof. exact (EscapingSpline.Espline_term sampler sampler_correct n). Qed.

End UniformX.
