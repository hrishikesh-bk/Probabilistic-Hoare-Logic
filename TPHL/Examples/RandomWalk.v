(** Biased random walk.

    [while 1 <= x do (toss(b, 1/4); if b then x := x + 1 else x := x - 1)].
    Started at [x = 1], the walk reaches [x = 0] with probability at least
    [1 - 2 / (3^(n+1) - 1)] for every [n > 0] ([Rwalk_term]); the bound
    comes from [W^LB] with the [n] regions [x = 1], ..., [x = n]: region [i]
    is [x = i + 1], so progress goes towards smaller indices.

    The regions, transitions, exits and solution are the nat-indexed
    functions [regions], [trans], [exits], [sol]; the while rule's side
    conditions are [helper1] (regions in the guard), [helper2]
    (disjointness), [helper3] (progress), [helper4] (body premise),
    [rw_sum] and [sol_ok] (the linear inequalities), [helper6] (value of
    the solution at [x = 1]). *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
Require Import PHL Examples.Lib Examples.PrAtoms.
Require Import Soundness.StateFacts Soundness.AssertionFacts Completeness.StructuralRules.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

(** * Local helpers *)

(** Embed a real-valued Coq term in a probabilistic formula. *)
Notation "'#(' x ')'" := (pconst x) (in custom tpf at level 0, x constr at level 200)
  : tphl_scope.

Ltac cdec :=
  let v := fresh "v" in let Hv := fresh "Hv" in
  intros v Hv; revert Hv; cunfold; cdestruct;
  rewrite ?Nat.eqb_eq, ?Nat.eqb_neq, ?Nat.leb_le, ?Nat.leb_gt, ?Nat.ltb_lt, ?Nat.ltb_ge in *;
  intuition (try congruence; try lia).

(** Concentration inside [c]: if all of [c]'s mass sits on [h] ([h] implies
    [c]), a formula [g] inside [c] that [h] decides has probability [Pr(h)]
    or 0. *)
Lemma Pr_cconc_in (ps : Pstate) (h c g : CFormula) :
  pstate_admissible ps -> Pr[ps] h = Pr[ps] c ->
  (forall v, satisfies v h -> satisfies v c) ->
  (forall v, satisfies v g -> satisfies v c) ->
  (forall v, satisfies v h -> satisfies v g) -> Pr[ps] g = Pr[ps] h.
Proof.
  intros Hps Hh _ Hg Hhg.
  pose proof (Pr_mono ps Hps h g Hhg). pose proof (Pr_mono ps Hps g c Hg). lra.
Qed.

Lemma Pr_cconc_out (ps : Pstate) (h c g : CFormula) :
  pstate_admissible ps -> Pr[ps] h = Pr[ps] c ->
  (forall v, satisfies v h -> satisfies v c) ->
  (forall v, satisfies v g -> satisfies v c) ->
  (forall v, satisfies v h -> ~ satisfies v g) -> Pr[ps] g = 0.
Proof.
  intros Hps Hh Hhc Hg Hhg.
  assert (Hd : forall v, ~ (satisfies v g /\ satisfies v h)) by (intros v [H1 H2]; exact (Hhg v H2 H1)).
  pose proof (Pr_disjoint ps Hps g h Hd).
  assert (Pr[ps] (c_or g h) <= Pr[ps] c).
  { apply Pr_mono; [exact Hps|]. intros v Hv. rewrite satisfies_or in Hv.
    destruct Hv; auto. }
  pose proof (Pr_nonneg ps g). lra.
Qed.

(** With all mass on [h], [Pr(h /\ g) = Pr(g)]. *)
Lemma Pr_and_true (ps : Pstate) (h g : CFormula) :
  pstate_admissible ps -> Pr[ps] h = Pr[ps] c_true -> Pr[ps] (c_and h g) = Pr[ps] g.
Proof.
  intros Hps Hh. rewrite (Pr_split ps Hps g h).
  assert (E1 : Pr[ps] (c_and h g) = Pr[ps] (c_and g h))
    by (apply Pr_ext; intro v; rewrite !satisfies_and; tauto).
  assert (E2 : Pr[ps] (c_and g (c_not h)) = 0).
  { apply (Pr_cconc_out ps h c_true _ Hps Hh); intros v.
    - intros _; apply satisfies_true.
    - intros _; apply satisfies_true.
    - intros Hv. rewrite satisfies_and, satisfies_not. tauto. }
  lra.
Qed.


(** Rewrite every [Pr g] in the goal using a hypothesis [Pr h = Pr c]. *)
Ltac cconc :=
  repeat match goal with
  | Hps : pstate_admissible ?ps, H : Pr[?ps] ?h = Pr[?ps] ?c |- context [Pr[?ps] ?g] =>
      tryif constr_eq g h then fail else
      tryif constr_eq g c then fail else
      first [ rewrite (Pr_cconc_in ps h c g Hps H) by cdec
            | rewrite (Pr_cconc_out ps h c g Hps H) by cdec ]
  end.

(** A formula probability already in canonical form. *)
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

Lemma Pc_nonneg ps g : 0 <= Pc ps g.
Proof. apply Pr_nonneg. Qed.

(** A finite conjunction of postconditions is derivable pointwise. *)
Lemma derive_finite_p_and pre (c : Cmd) m (f : nat -> PFormula) :
  (forall j, (j < m)%nat -> hoare_derivable pre c (f j)) ->
  hoare_derivable pre c (finite_p_and m f).
Proof.
  induction m as [|m IH]; intros H; cbn [finite_p_and].
  - apply derive_true.
  - apply HAnd; [apply IH; intros j Hj; apply H; lia | apply H; lia].
Qed.

Module RandomWalk.

Notation x := (dom_program_var "x").
Notation b := (bool_program_var "b").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").

Definition body : Cmd :=
  <{ b toss 0.25; if b then x := x + #(1%nat) else x := x - #(1%nat) end }>.

Definition guard : CFormula := \{ #(1%nat) <= x \}.

Definition RandomWalk : Cmd := CWhile guard body.

Ltac rw_side := ptrans; pvalid; split_hyps; cconc; try lra.

(** * The branches *)

Theorem ifthen_01 (k : nat) :
  hoare_derivable
    {{ ((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true)) /\ y1 = 0.25 }}
    <{ x := x + #(1%nat) }>
    {{ (prob (x = #((k + 1)%nat))) = y1 }}.
Proof. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

Theorem ifthen_02 (k : nat) :
  hoare_derivable
    {{ ((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true)) /\ y2 = 0 }}
    <{ x := x - #(1%nat) }>
    {{ (prob (x = #((k + 1)%nat))) = y2 }}.
Proof. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

(** Side condition of the [HConseqLeft] into the conditioned precondition
    of [HIfEq]. *)
Definition if_atoms (k : nat) : list CFormula :=
  cons \{ x = k /\ b \} (cons \{ x = k /\ ~ b \}
    (cons (FProgBool b) (cons (c_not (FProgBool b)) nil))).

Ltac if_side k :=
  ptrans; pvalid; split_hyps;
  let l := eval unfold if_atoms in (if_atoms k) in pcanon l; unfold Pc in *;
  repeat split; lra.

Theorem ifthen_0_int (k : nat) :
  hoare_derivable
    {{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
         ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\
        y1 = 0.25) /\ y2 = 0 }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ y1 + y2 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseqLeft with
    (pre' := if_precondition
               {{ ((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true)) /\ y1 = 0.25 }}
               {{ ((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true)) /\ y2 = 0 }}
               (FProgBool b)).
  - if_side k.
  - apply HIfEq.
    + apply HConseqRight with (post := {{ (prob (x = #((k + 1)%nat))) = y1 }});
        [ptrans; pvalid; lra | apply ifthen_01].
    + apply HConseqRight with (post := {{ (prob (x = #((k + 1)%nat))) = y2 }});
        [ptrans; pvalid; lra | apply ifthen_02].
Qed.

Theorem ifthen_0 (k : nat) :
  hoare_derivable
    {{ ((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b))) }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ 0.25 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 0.25) {{ (((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\ y1 = 0.25 }})
    (eta2 := subst_prob_pformula y1 (PConst 0.25)
               (subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = #((k + 1)%nat))) }})).
  - ptrans; pvalid. split_hyps. repeat split; lra.
  - apply (HInstantiate y1 0.25).
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst 0) {{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\ y1 = 0.25) /\ y2 = 0 }})
      (eta2 := subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = #((k + 1)%nat))) }}).
    + ptrans; pvalid. split_hyps. repeat split; lra.
    + apply (HInstantiate y2 0). apply (ifthen_0_int k).
    + intros ps _. apply psatisfies_impl. tauto.
  - ptrans; pvalid. lra.
Qed.

Theorem ifthen_11 (k : nat) :
  hoare_derivable
    {{ ((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true)) /\ y1 = 0 }}
    <{ x := x + #(1%nat) }>
    {{ (prob (x = #((k - 1)%nat))) = y1 }}.
Proof. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

Theorem ifthen_12 (k : nat) : (k > 0)%nat ->
  hoare_derivable
    {{ ((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true)) /\ y2 = 0.75 }}
    <{ x := x - #(1%nat) }>
    {{ (prob (x = #((k - 1)%nat))) = y2 }}.
Proof. intros Hk. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

Theorem ifthen_1_int (k : nat) : (k > 0)%nat ->
  hoare_derivable
    {{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
         ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\
        y1 = 0) /\ y2 = 0.75 }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ y1 + y2 = (prob (x = #((k - 1)%nat))) }}.
Proof.
  intros Hk.
  apply HConseqLeft with
    (pre' := if_precondition
               {{ ((prob (x = k)) = 0.25 /\ (prob (x = k)) = (prob true)) /\ y1 = 0 }}
               {{ ((prob (x = k)) = 0.75 /\ (prob (x = k)) = (prob true)) /\ y2 = 0.75 }}
               (FProgBool b)).
  - if_side k.
  - apply HIfEq.
    + apply HConseqRight with (post := {{ (prob (x = #((k - 1)%nat))) = y1 }});
        [ptrans; pvalid; lra | apply ifthen_11].
    + apply HConseqRight with (post := {{ (prob (x = #((k - 1)%nat))) = y2 }});
        [ptrans; pvalid; lra | apply (ifthen_12 k Hk)].
Qed.

Theorem ifthen_1 (k : nat) : (k > 0)%nat ->
  hoare_derivable
    {{ ((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b))) }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ 0.75 = (prob (x = #((k - 1)%nat))) }}.
Proof.
  intros Hk.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 0) {{ (((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\ y1 = 0 }})
    (eta2 := subst_prob_pformula y1 (PConst 0)
               (subst_prob_pformula y2 (PConst 0.75) {{ y1 + y2 = (prob (x = #((k - 1)%nat))) }})).
  - ptrans; pvalid. split_hyps. repeat split; lra.
  - apply (HInstantiate y1 0).
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst 0.75) {{ ((((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b)))) /\ y1 = 0) /\ y2 = 0.75 }})
      (eta2 := subst_prob_pformula y2 (PConst 0.75) {{ y1 + y2 = (prob (x = #((k - 1)%nat))) }}).
    + ptrans; pvalid. split_hyps. repeat split; lra.
    + apply (HInstantiate y2 0.75). apply (ifthen_1_int k Hk).
    + intros ps _. apply psatisfies_impl. tauto.
  - ptrans; pvalid. lra.
Qed.

Theorem ifthen_void1 (k k1 : nat) : (k > 0)%nat -> k1 <> (k - 1)%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (prob (x = k)) = (prob true) /\ y1 = 0 }}
    <{ x := x + #(1%nat) }>
    {{ y1 = (prob (x = k1)) }}.
Proof. intros Hk H1 H2. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

Theorem ifthen_void2 (k k1 : nat) : (k > 0)%nat -> k1 <> (k - 1)%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (prob (x = k)) = (prob true) /\ y2 = 0 }}
    <{ x := x - #(1%nat) }>
    {{ y2 = (prob (x = k1)) }}.
Proof. intros Hk H1 H2. eapply HConseqLeft; [|apply HDomAssign]. rw_side. Qed.

Theorem ifthen_void_int (k k1 : nat) : (k > 0)%nat -> k1 <> (k - 1)%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (((prob (x = k /\ b)) = (prob b) /\ (prob (x = k /\ ~ b)) = (prob (~ b))) /\
        y1 = 0) /\ y2 = 0 }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ y1 + y2 = (prob (x = k1)) }}.
Proof.
  intros Hk H1 H2.
  apply HConseqLeft with
    (pre' := if_precondition {{ (prob (x = k)) = (prob true) /\ y1 = 0 }}
                             {{ (prob (x = k)) = (prob true) /\ y2 = 0 }} (FProgBool b)).
  - if_side k.
  - apply HIfEq; [apply ifthen_void1 | apply ifthen_void2]; assumption.
Qed.

Theorem ifthen_void (k k1 : nat) : (k > 0)%nat -> k1 <> (k - 1)%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (prob (x = k /\ b)) = (prob b) /\ (prob (x = k /\ ~ b)) = (prob (~ b)) }}
    <{ if b then x := x + #(1%nat) else x := x - #(1%nat) end }>
    {{ 0 = (prob (x = k1)) }}.
Proof.
  intros Hk H1 H2.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 0) {{ ((prob (x = k /\ b)) = (prob b) /\ (prob (x = k /\ ~ b)) = (prob (~ b))) /\ y1 = 0 }})
    (eta2 := subst_prob_pformula y1 (PConst 0)
               (subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = k1)) }})).
  - ptrans; pvalid. split_hyps. repeat split; lra.
  - apply (HInstantiate y1 0).
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst 0) {{ (((prob (x = k /\ b)) = (prob b) /\ (prob (x = k /\ ~ b)) = (prob (~ b))) /\ y1 = 0) /\ y2 = 0 }})
      (eta2 := subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = k1)) }}).
    + ptrans; pvalid. split_hyps. repeat split; lra.
    + apply (HInstantiate y2 0). apply (ifthen_void_int k k1 Hk H1 H2).
    + intros ps _. apply psatisfies_impl. tauto.
  - ptrans; pvalid. lra.
Qed.

(** * The body *)

Theorem bodyvoid (k k1 : nat) : (k > 0)%nat -> k1 <> (k - 1)%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}
    body
    {{ 0 = (prob (x = k1)) }}.
Proof.
  intros Hk H1 H2. apply HSeq with (eta2 := {{ (prob (x = k)) = (prob true) }}).
  - eapply HConseqLeft; [|apply HBoolToss; unfold coin_probability_valid; lra].
    rw_side.
  - apply HConseqLeft with
      (pre' := {{ (prob (x = k /\ b)) = (prob b) /\ (prob (x = k /\ ~ b)) = (prob (~ b)) }}).
    + ptrans; pvalid. split_hyps. split; apply (Pr_and_true ps _ _ Hps H).
    + apply (ifthen_void k k1 Hk H1 H2).
Qed.

Theorem body0 (k : nat) :
  hoare_derivable
    {{ (prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}
    body
    {{ 0.25 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HSeq with (eta2 := {{ ((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b))) }}).
  - eapply HConseqLeft; [|apply HBoolToss; unfold coin_probability_valid; lra].
    rw_side; repeat split; lra.
  - apply ifthen_0.
Qed.

Theorem body1 (k : nat) : (k > 0)%nat ->
  hoare_derivable
    {{ (prob (k = x)) = 1 /\ (prob (k = x)) = (prob true) }}
    body
    {{ 0.75 = (prob (x = #((k - 1)%nat))) }}.
Proof.
  intros Hk. apply HSeq with (eta2 := {{ ((prob (x = k /\ b)) = 0.25 /\ (prob (x = k /\ b)) = (prob b)) /\
       ((prob (x = k /\ ~ b)) = 0.75 /\ (prob (x = k /\ ~ b)) = (prob (~ b))) }}).
  - eapply HConseqLeft; [|apply HBoolToss; unfold coin_probability_valid; lra].
    rw_side; repeat split; lra.
  - apply (ifthen_1 k Hk).
Qed.

(** * The while rule *)

(** Region [i] is [x = i + 1]. *)
Definition regions (i : nat) : CFormula := \{ x = #(S i) \}.

(** From [x = i + 1]: down to region [i - 1] with 3/4, up to [i + 1] with
    1/4. *)
Definition trans (i j : nat) : R :=
  if Nat.eqb (S j) i then 0.75 else if Nat.eqb j (S i) then 0.25 else 0.

(** Exit into [x = 0] with 3/4 from [x = 1]. *)
Definition exits (i : nat) : R := if Nat.eqb i 0 then 0.75 else 0.

(** [f n v = 1 - (3^v - 1) / (3^(n+1) - 1)] solves the recurrence
    [f v = 3/4 f (v-1) + 1/4 f (v+1)] with [f 0 = 1], [f (n+1) = 0]. *)
Definition f (n v : nat) : R := 1 - (3 ^ v - 1) / (3 ^ (n + 1) - 1).

(** The solution at region [i]. *)
Definition sol (n i : nat) : R := f n (S i).

Lemma D_pos n : 0 < 3 ^ (n + 1) - 1.
Proof.
  rewrite Nat.add_1_r. cbn [pow]. pose proof (pow_R1_Rle 3 n ltac:(lra)). lra.
Qed.

Lemma f_rec n v : f n (S v) = 0.75 * f n v + 0.25 * f n (S (S v)).
Proof.
  unfold f. pose proof (D_pos n). cbn [pow].
  replace 0.75 with (3 / 4) by lra. replace 0.25 with (1 / 4) by lra.
  field. lra.
Qed.

Lemma f_0 n : f n 0 = 1.
Proof. unfold f. cbn [pow]. replace (1 - 1) with 0 by lra. unfold Rdiv. rewrite Rmult_0_l. lra. Qed.

Lemma f_top n : f n (S n) = 0.
Proof.
  unfold f. pose proof (D_pos n). rewrite Nat.add_1_r. field. rewrite <- Nat.add_1_r. lra.
Qed.

Lemma f_bounds n v : (v <= S n)%nat -> 0 <= f n v <= 1.
Proof.
  intros Hv. unfold f. pose proof (D_pos n) as HD.
  pose proof (pow_R1_Rle 3 v ltac:(lra)) as H1.
  pose proof (Rle_pow 3 v (n + 1) ltac:(lra) ltac:(lia)) as H2.
  set (D := 3 ^ (n + 1) - 1) in *.
  assert (0 <= (3 ^ v - 1) / D).
  { unfold Rdiv. apply Rmult_le_pos; [lra|]. left; apply Rinv_0_lt_compat; lra. }
  assert ((3 ^ v - 1) / D <= 1).
  { apply (Rmult_le_reg_r D); [lra|]. unfold Rdiv.
    rewrite Rmult_assoc, Rinv_l by lra. unfold D in *; lra. }
  lra.
Qed.

(** ** Finite sums *)

Lemma frs_ext m (g h : nat -> R) :
  (forall j, (j < m)%nat -> g j = h j) -> finite_r_sum m g = finite_r_sum m h.
Proof.
  induction m as [|m IH]; intros H; cbn [finite_r_sum]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H m) by lia. reflexivity.
Qed.

Lemma frs_add m (g h : nat -> R) :
  finite_r_sum m (fun j => g j + h j) = finite_r_sum m g + finite_r_sum m h.
Proof. induction m as [|m IH]; cbn [finite_r_sum]; [lra|rewrite IH; lra]. Qed.

Lemma frs_ind m a (c : R) :
  finite_r_sum m (fun j => if Nat.eqb j a then c else 0) = if Nat.ltb a m then c else 0.
Proof.
  induction m as [|m IH]; cbn [finite_r_sum].
  - destruct (Nat.ltb_spec a 0); [lia|reflexivity].
  - rewrite IH. destruct (Nat.ltb_spec a m), (Nat.ltb_spec a (S m)), (Nat.eqb_spec m a);
      try lia; lra.
Qed.

Lemma rw_sum n i : (i < n)%nat ->
  finite_r_sum n (fun j => trans i j * sol n j) =
  (match i with O => 0 | S i' => 0.75 * sol n i' end) +
  (if Nat.ltb (S i) n then 0.25 * sol n (S i) else 0).
Proof.
  intros Hi. unfold trans. destruct i as [|i'].
  - rewrite (frs_ext n _ (fun j => if Nat.eqb j 1 then 0.25 * sol n 1 else 0)).
    + rewrite frs_ind. lra.
    + intros j _. destruct (Nat.eqb_spec (S j) 0); [lia|].
      destruct (Nat.eqb_spec j 1); [subst; reflexivity | lra].
  - rewrite (frs_ext n _ (fun j => (if Nat.eqb j i' then 0.75 * sol n i' else 0) +
                                   (if Nat.eqb j (S (S i')) then 0.25 * sol n (S (S i')) else 0))).
    + rewrite frs_add, !frs_ind. destruct (Nat.ltb_spec i' n); [|lia]. reflexivity.
    + intros j _. destruct (Nat.eqb_spec (S j) (S i')), (Nat.eqb_spec j i'),
        (Nat.eqb_spec j (S (S i'))); subst; try lia; lra.
Qed.

(** The linear inequalities of [W^LB]; they hold
    with equality. *)
Lemma sol_ok n : (n > 0)%nat -> while_lower_solution n (sol n) trans exits.
Proof.
  intros Hn i Hi. split; [|unfold sol; apply f_bounds; lia].
  rewrite rw_sum by exact Hi. unfold sol, exits.
  destruct i as [|i'].
  - cbn [Nat.eqb]. rewrite (f_rec n 0), f_0.
    destruct (Nat.ltb_spec 1 n).
    + lra.
    + assert (n = 1)%nat by lia; subst. rewrite f_top. lra.
  - cbn [Nat.eqb]. rewrite (f_rec n (S i')).
    destruct (Nat.ltb_spec (S (S i')) n).
    + lra.
    + assert (S (S (S i')) = S n) as -> by lia. rewrite f_top. lra.
Qed.

(** ** Side conditions *)

Lemma helper1 n : while_regions_in_guard n guard regions.
Proof. unfold while_regions_in_guard, cformula_valid, guard, regions. intros i Hi. cdecide. Qed.

Lemma helper2 n : while_regions_disjoint n regions.
Proof. unfold while_regions_disjoint, cformula_valid, regions. intros i j Hi Hj. cdecide. Qed.

Lemma helper3 n : while_progress n trans exits.
Proof.
  intros i Hi. unfold exits, trans. destruct i as [|i'].
  - left; cbn; lra.
  - right. exists i'. split; [lia|]. rewrite Nat.eqb_refl. lra.
Qed.

(** Side condition: [Box(x = k) /\ Pr(tt) = 1] gives the precondition
    [Pr(k = x) = 1 /\ Pr(k = x) = Pr(tt)] of [body0], [body1], [bodyvoid]. *)
Ltac region_pre :=
  unfold regions; ptrans; pvalid; split_hyps;
  match goal with Hps : pstate_admissible ?ps, H : Pr[?ps] ?g = Pr[?ps] _ |- _ =>
    pcanon [g; \{ true \}] end;
  unfold Pc in *; split; lra.

(** The body premise of [W^LB] for region [i]: one
    conjunct per region [j], from [body0] (to [x = k + 1]), [body1] (to
    [x = k - 1]) or [bodyvoid] (anywhere else), and the exit conjunct from
    [body1] at [x = 1] or [bodyvoid] (with [k1 = 0]) elsewhere. *)
Lemma helper4 n i : (i < n)%nat ->
  hoare_derivable (p_concentrated_unit (regions i)) body
    (while_body_post_lower n regions (trans i) guard \{ x = #(0%nat) \} (exits i)).
Proof.
  intros Hi. unfold while_body_post_lower. apply HAnd.
  - apply derive_finite_p_and. intros j Hj. unfold trans.
    destruct (Nat.eqb_spec (S j) i); [|destruct (Nat.eqb_spec j (S i))].
    + subst i. eapply HConseq; [|apply (body1 (S (S j))); lia|].
      * region_pre.
      * unfold regions. ptrans; pvalid. replace (S (S j) - 1)%nat with (S j) in H by lia. lra.
    + subst j. eapply HConseq; [|apply (body0 (S i))|].
      * region_pre.
      * unfold regions. ptrans; pvalid. replace (S i + 1)%nat with (S (S i)) in H by lia. lra.
    + eapply HConseq; [|apply (bodyvoid (S i) (S j)); lia|].
      * region_pre.
      * unfold regions. ptrans; pvalid. lra.
  - unfold exits. destruct (Nat.eqb_spec i 0) as [->|Hne].
    + apply HConseqLeft with (pre' := {{ (prob (#(1%nat) = x)) = 1 /\ (prob (#(1%nat) = x)) = (prob true) }}).
      * region_pre.
      * eapply HConseqRight; [|apply (body1 1); lia].
        unfold guard. ptrans; pvalid.
        match goal with H : _ = Pr[ps] ?h |- _ <= Pr[ps] ?g => rewrite (Pr_ext ps g h) by cdecide end.
        rewrite <- H. lra.
    + eapply HConseq; [|apply (bodyvoid (S i) 0); lia|].
      * region_pre.
      * unfold guard. ptrans; pvalid.
        match goal with H : _ = Pr[ps] ?h |- _ <= Pr[ps] ?g => rewrite (Pr_ext ps g h) by cdecide end.
        lra.
Qed.

(** The solution at [x = 1]. *)
Lemma helper6 n : sol n 0 = 1 - 2 / (3 ^ (n + 1) - 1).
Proof. unfold sol, f. cbn [pow]. replace (3 * 1 - 1) with 2 by lra. reflexivity. Qed.

(** * Termination *)

Theorem Rwalk_term_int (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (#(1%nat) <= x /\ x = #(1%nat))) >= y1 /\
       (prob (#(1%nat) <= x /\ x = #(1%nat))) = (prob true) }}
    RandomWalk
    {{ #(1 - 2 / (3 ^ (n + 1) - 1)) * y1 <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn.
  eapply HConseqRight; [|eapply HConseqLeft;
    [|apply (HWhileLower n 0 guard \{ x = #(0%nat) \} body regions (sol n) exits trans y1)]].
  - rewrite <- helper6. ptrans; pvalid. lra.
  - unfold guard, regions. ptrans; pvalid; split_hyps.
    pcanon [\{ #(1%nat) <= x /\ x = #(1%nat) \}; \{ true \}]. unfold Pc in *. split; lra.
  - exact Hn.
  - apply helper1.
  - apply helper2.
  - apply helper3.
  - exact (helper4 n).
  - exact (sol_ok n Hn).
Qed.

Theorem Rwalk_term_y (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true) }}
    RandomWalk
    {{ #(1 - 2 / (3 ^ (n + 1) - 1)) * y1 <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn. eapply HConseqLeft; [|apply (Rwalk_term_int n Hn)].
  ptrans; pvalid; split_hyps. pcanon [\{ x = #(1%nat) \}; \{ true \}]. unfold Pc in *.
  split; lra.
Qed.

(** Started at [x = 1], the walk reaches 0 with probability at least
    [1 - 2 / (3^(n+1) - 1)], for every [n > 0]. *)
Theorem Rwalk_term (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (x = #(1%nat))) = 1 /\ (prob (x = #(1%nat))) = (prob true) }}
    RandomWalk
    {{ #(1 - 2 / (3 ^ (n + 1) - 1)) <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn.
  apply HConseqLeft with
    (pre' := {{ (prob (x = #(1%nat))) >= 1 /\ (prob (x = #(1%nat))) = (prob true) }}).
  { ptrans; pvalid; split_hyps. split; lra. }
  assert (Hy : hoare_derivable
                 {{ ((prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true)) /\ y1 = 1 }}
                 RandomWalk
                 {{ #(1 - 2 / (3 ^ (n + 1) - 1)) * y1 <= (prob (x = #(0%nat))) }}).
  { apply HConseqLeft with
      (pre' := {{ (prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true) }}).
    - ptrans; pvalid; split_hyps. split; lra.
    - apply (Rwalk_term_y n Hn). }
  eapply HConseq; [|apply (HInstantiate y1 1 _ _ _ Hy)|].
  - ptrans; pvalid; split_hyps. repeat split; lra.
  - ptrans; pvalid. lra.
Qed.

End RandomWalk.
