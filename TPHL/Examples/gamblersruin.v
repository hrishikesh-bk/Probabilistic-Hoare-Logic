(** Gambler's ruin (ported from the old [gamblersruin.v]).

    The body: if [x0 >= 1] then toss [b] with rate 1/3 and move [x0] up on
    heads, down on tails; otherwise skip.  The main theorem bounds the
    probability of reaching 3 from 1 by 1/7 with [W^UB].

    The proofs follow the old ones rule by rule: the same rules are applied
    in the same order with the same intermediate assertions, written in TPHL
    syntax.  Old names map as [HTAsgn] -> [HDomAssign] ([tasgn_pt] ->
    [subst_dom_pformula]), [HBToss] -> [HBoolToss] ([btoss_pt] ->
    [toss_pformula]), [HIfThen] -> [HIfEq] ([psfBpsf] -> [if_precondition]),
    [HWhileUB] -> [HWhileUpper], [eta_update_y_p] -> [subst_prob_pformula].
    The old [RigidUnchanged], [AddRigidRight] and [AddRigidBoth] are proved
    below from the same rules as before.  Consequence side conditions are
    proved by the tactic [gside].

    Differences from the old proofs:
    - [HElimv] is always preceded by [HConseqLeft] to the precondition
      [subst_prob_pformula y p eta]; the old proof sometimes rewrote the goal
      with an equation instead.
    - The while rules take the body precondition [p_concentrated_unit g]
      ([Pr(g) = Pr(tt) /\ Pr(tt) = 1]) instead of the old
      [Pr(g) = 1 /\ Pr(g) = Pr(tt)], so each case of [ant_1to3] starts with
      [HConseqLeft] to the helper theorems' precondition.  The body
      postconditions are [finite_p_and] conjunctions with a leading [p_true]
      (the old vectors ended with [True]); in both versions it is absorbed by
      the consequence step on one component.
    - [W^UB]'s precondition is [Box(beta /\ G_k) /\ Pr(tt) <= y] (old:
      [Pr(beta /\ G_k) <= y /\ Pr(beta /\ G_k) = Pr(tt)]); the intermediate
      assertion of the [HConseq] step in [Gambler3_UB] has the new shape.
    - [xgeq1]'s postcondition is stated as [A /\ (B /\ C)]; the old proof
      rewrote it to [(A /\ B) /\ C] before splitting; here that rewrite is an
      [HConseqRight] step.
    - [xeq1_UB]'s second part and [ant_1to3] use [proj1]/[proj2] where the
      old proof applied a conjunction of triples directly. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Setoid.
Require Import PHL Examples.Lib Examples.PrAtoms.
Require Import Soundness.StateFacts Soundness.AssertionFacts.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module GamblersRuin.

Notation "x >= y" := (c_le y x) (in custom tcf at level 60, no associativity) : tphl_scope.

Definition neqnat (a c : nat) : Prop := a <> c.

Notation b := (bool_program_var "b").
Notation x := (dom_program_var "x").
Notation y := (prob_logic_var "y").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").
Notation y3 := (prob_logic_var "y3").
Notation y4 := (prob_logic_var "y4").

Definition half : R := 1/2.
Definition twothird : R := 2/3.
Definition onethird : R := 1/3.
Definition seventh : R := 1/7.

Definition GamblersRuin_Body (x0 : DomProgramVar) : Cmd :=
  <{ if (x0 >= #(1%nat))
     then (b toss (1/3);
           (if b then (x0 := x0 + #(1%nat)) else (x0 := x0 - #(1%nat)) end))
     else skip
     end }>.

Definition then_branch (x0 : DomProgramVar) : Cmd :=
  <{ b toss (1/3); (if b then (x0 := x0 + #(1%nat)) else (x0 := x0 - #(1%nat)) end) }>.

(** * Side conditions *)

Lemma Pr_conc_false (ps : Pstate) (h g : CFormula) : pstate_admissible ps -> Pr[ps] h = Pr[ps] c_true ->
  (forall v, satisfies v h -> ~ satisfies v g) -> Pr[ps] g = 0.
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

Lemma tt_iff : (true = true) <-> True.
Proof. tauto. Qed.
Lemma ft_iff : (false = true) <-> False.
Proof. split; [discriminate | tauto]. Qed.
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

(** Evaluate a closed propositional formula ([True], [False], [->],
    [<->]) by rewriting; [tauto] is slow to refute such formulas. *)
Lemma and_T_l (P : Prop) : (True /\ P) <-> P.
Proof. tauto. Qed.
Lemma and_T_r (P : Prop) : (P /\ True) <-> P.
Proof. tauto. Qed.
Lemma and_F_l (P : Prop) : (False /\ P) <-> False.
Proof. tauto. Qed.
Lemma and_F_r (P : Prop) : (P /\ False) <-> False.
Proof. tauto. Qed.
Lemma or_T_l (P : Prop) : (True \/ P) <-> True.
Proof. tauto. Qed.
Lemma or_T_r (P : Prop) : (P \/ True) <-> True.
Proof. tauto. Qed.
Lemma or_F_l (P : Prop) : (False \/ P) <-> P.
Proof. tauto. Qed.
Lemma or_F_r (P : Prop) : (P \/ False) <-> P.
Proof. tauto. Qed.
Lemma not_T : (~ True) <-> False.
Proof. tauto. Qed.
Lemma not_F : (~ False) <-> True.
Proof. tauto. Qed.

Ltac cleaf :=
  rewrite ?tt_iff, ?ft_iff;
  repeat first [ rewrite imp_T_l | rewrite imp_F_l | rewrite imp_T_r
               | rewrite iff_T_l | rewrite iff_T_r | rewrite iff_F_l | rewrite iff_F_r
               | rewrite and_T_l | rewrite and_T_r | rewrite and_F_l | rewrite and_F_r
               | rewrite or_T_l | rewrite or_T_r | rewrite or_F_l | rewrite or_F_r
               | rewrite not_T | rewrite not_F ];
  exact I.

(** Decide a classical validity over symbolic atoms: split each atom (and
    each Boolean variable) by its specification; inconsistent cases go to
    [lia], the rest are closed formulas, evaluated by [cleaf] (as in
    [UniformX.v]). *)
Ltac cfast :=
  let v := fresh "v" in
  intro v; cunfold;
  repeat match goal with
  | |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c)
  | |- context [Nat.leb ?a ?c] => destruct (Nat.leb_spec a c)
  | |- context [Nat.ltb ?a ?c] => destruct (Nat.ltb_spec a c)
  | |- context [bool_program_values ?w ?bb] => destruct (bool_program_values w bb)
  end;
  first [ exfalso; lia | cleaf | tauto ].

(** With all mass on [h], formulas that agree on [h] have the same
    probability (the old proofs' "rewrite with [x0 = n]" step). *)
Lemma Pr_conc_equiv (ps : Pstate) (h : CFormula) :
  pstate_admissible ps -> Pr[ps] h = Pr[ps] c_true ->
  forall g g', (forall v, satisfies v h -> (satisfies v g <-> satisfies v g')) ->
  Pr[ps] g = Pr[ps] g'.
Proof.
  intros Hps Hh g g' Heq.
  assert (Hon : forall f, Pr[ps] f = Pr[ps] (c_and f h)).
  { intros f. rewrite (Pr_split ps Hps f h).
    rewrite (Pr_conc_false ps h (c_and f (c_not h)) Hps Hh); [lra|].
    intros v Hv Hf. rewrite satisfies_and, satisfies_not in Hf. tauto. }
  rewrite (Hon g), (Hon g'). apply Pr_ext. intros v. rewrite !satisfies_and.
  split; intros [H1 H2]; split; try exact H2; apply (Heq v H2); exact H1.
Qed.

(** [cfast] without the [tauto] fallback: fails fast on a wrong guess. *)
Ltac cfast_quick :=
  let v := fresh "v" in
  intro v; cunfold;
  repeat match goal with
  | |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c)
  | |- context [Nat.leb ?a ?c] => destruct (Nat.leb_spec a c)
  | |- context [Nat.ltb ?a ?c] => destruct (Nat.ltb_spec a c)
  | |- context [bool_program_values ?w ?bb] => destruct (bool_program_values w bb)
  end;
  first [ exfalso; lia | cleaf ].

Definition Pc (ps : Pstate) (g : CFormula) : R := Pr[ps] g.

Ltac pconc_one ps K X Gs :=
  lazymatch Gs with
  | cons ?G ?rest =>
      first
        [ let E := fresh "E" in
          assert (E : Pr[ps] X = Pc ps G) by (unfold Pc; apply K; cfast_quick);
          rewrite E in *; clear E
        | pconc_one ps K X rest ]
  | nil =>
      let E := fresh "E" in
      assert (E : Pr[ps] X = 0) by (rewrite <- (Pr_false ps); apply K; cfast_quick);
      rewrite E in *; clear E
  end.

(** A side condition whose hypotheses put all mass on [h]: reduce every
    probability to one of the canonical formulas [Gs] (or 0) under [h]. *)
Tactic Notation "gconc" constr(Gs) :=
  unfold twothird, onethird, half, seventh in *;
  ptrans; pvalid; split_hyps;
  match goal with
  | Hps : pstate_admissible ?ps, Hh : Pr[?ps] ?h' = Pr[?ps] ?t |- _ =>
      lazymatch t with c_true => idtac | FImpl FFalse FFalse => idtac end;
      let K := fresh "K" in
      pose proof (Pr_conc_equiv ps h' Hps Hh) as K; clear Hh;
      repeat match goal with
      | |- context [Pr[ps] ?X] => pconc_one ps K X Gs
      | H : context [Pr[ps] ?X] |- _ => pconc_one ps K X Gs
      end;
      pose proof (Pr_true_le1 ps Hps)
  end;
  unfold Pc in *; repeat split; lra.

(** Finite additivity (the old [fin_additivity] steps). *)
Lemma Pr_sum2 (ps : Pstate) (g1 g2 g : CFormula) : pstate_admissible ps ->
  (forall v, ~ (satisfies v g1 /\ satisfies v g2)) ->
  (forall v, satisfies v g <-> satisfies v g1 \/ satisfies v g2) ->
  Pr[ps] g = Pr[ps] g1 + Pr[ps] g2.
Proof.
  intros Hps Hd Hg. rewrite <- (Pr_disjoint ps Hps g1 g2 Hd). apply Pr_ext.
  intros v. rewrite satisfies_or. apply Hg.
Qed.

Lemma Pr_sum3_le (ps : Pstate) (g1 g2 g3 : CFormula) : pstate_admissible ps ->
  (forall v, ~ (satisfies v g1 /\ satisfies v g2)) ->
  (forall v, ~ (satisfies v g1 /\ satisfies v g3)) ->
  (forall v, ~ (satisfies v g2 /\ satisfies v g3)) ->
  Pr[ps] g1 + Pr[ps] g2 + Pr[ps] g3 <= Pr[ps] c_true.
Proof.
  intros Hps H12 H13 H23.
  rewrite <- (Pr_disjoint ps Hps g1 g2 H12).
  rewrite <- (Pr_disjoint ps Hps (c_or g1 g2) g3).
  - apply Pr_le_true. exact Hps.
  - intros v [Ho H3]. rewrite satisfies_or in Ho. destruct Ho as [H1|H2].
    + exact (H13 v (conj H1 H3)).
    + exact (H23 v (conj H2 H3)).
Qed.

Ltac pext_one ps X Gs :=
  lazymatch Gs with
  | cons ?G ?rest =>
      first
        [ let E := fresh "E" in
          assert (E : Pr[ps] X = Pc ps G) by (unfold Pc; apply Pr_ext; cfast_quick);
          rewrite E in *; clear E
        | pext_one ps X rest ]
  end.

(** Rewrite every probability to one of the formulas [Gs] (an equivalence
    check each), leaving the arithmetic to the caller. *)
Tactic Notation "gext" constr(Gs) :=
  unfold twothird, onethird, half, seventh in *;
  ptrans; pvalid; split_hyps;
  match goal with Hps : pstate_admissible ?ps |- _ =>
    repeat match goal with
    | |- context [Pr[ps] ?X] => pext_one ps X Gs
    | H : context [Pr[ps] ?X] |- _ => pext_one ps X Gs
    end;
    pose proof (Pr_true_le1 ps Hps)
  end.

(** A truth assignment of the atoms that no state satisfies has
    probability 0 (e.g. [x0 = n] together with [x0 + 1 = n - 1]). *)
Lemma Patom_impossible ps L :
  (forall v, ~ satisfies v (conj_lits L)) -> Patom ps L = 0.
Proof.
  intros H. unfold Patom. rewrite <- (Pr_false ps). apply Pr_ext.
  intros v. split; [intros Hv; exfalso; exact (H v Hv) | cbn; tauto].
Qed.

Ltac kill_impossible :=
  repeat match goal with
  | |- context [Patom ?ps ?L] =>
      rewrite (Patom_impossible ps L) in * by (cbn [conj_lits lit_formula fst snd]; cfast)
  | H : context [Patom ?ps ?L] |- _ =>
      rewrite (Patom_impossible ps L) in * by (cbn [conj_lits lit_formula fst snd]; cfast)
  end.

(** Nonnegativity of every atom probability in the goal and hypotheses. *)
Ltac patoms_nonneg :=
  repeat match goal with
  | |- context [Patom ?ps ?L] =>
      lazymatch goal with _ : 0 <= Patom ps L |- _ => fail | _ => pose proof (Patom_nonneg ps L) end
  | _ : context [Patom ?ps ?L] |- _ =>
      lazymatch goal with _ : 0 <= Patom ps L |- _ => fail | _ => pose proof (Patom_nonneg ps L) end
  end.

(** Split each probability over the truth assignments of [atoms]
    ([Pr_partition]) and decide every case with [cfast].  Unlike [patoms],
    this works when formulas mention a variable [x0] or symbolic constants
    such as [n - 1]. *)
Lemma cell_full ps L g :
  (forall v, satisfies v (conj_lits L) -> satisfies v g) ->
  Pr[ps] (c_and (conj_lits L) g) = Patom ps L.
Proof.
  intros H. unfold Patom. apply Pr_ext. intros v. rewrite satisfies_and.
  pose proof (H v). tauto.
Qed.

Lemma cell_empty ps L g :
  (forall v, satisfies v (conj_lits L) -> ~ satisfies v g) ->
  Pr[ps] (c_and (conj_lits L) g) = 0.
Proof.
  intros H. rewrite <- (Pr_false ps). apply Pr_ext. intros v. rewrite satisfies_and.
  pose proof (H v). cbn [satisfies]. tauto.
Qed.

Ltac cells_split ps Hps atoms :=
  repeat match goal with
  | H : context [Pr[ps] ?g] |- _ =>
      lazymatch g with
      | c_and (conj_lits _) _ => fail
      | _ => rewrite (Pr_partition ps Hps atoms g) in H
      end
  | |- context [Pr[ps] ?g] =>
      lazymatch g with
      | c_and (conj_lits _) _ => fail
      | _ => rewrite (Pr_partition ps Hps atoms g)
      end
  end;
  cbn [rsum assignments map app] in *.

Ltac cell_side := cbn [conj_lits lit_formula fst snd]; cfast.

Ltac cells_decide :=
  repeat match goal with
  | |- context [Pr[?ps] (c_and (conj_lits ?L) ?g)] =>
      first [ rewrite (cell_full ps L g) in * by cell_side
            | rewrite (cell_empty ps L g) in * by cell_side ]
  | H : context [Pr[?ps] (c_and (conj_lits ?L) ?g)] |- _ =>
      first [ rewrite (cell_full ps L g) in * by cell_side
            | rewrite (cell_empty ps L g) in * by cell_side ]
  end.

(** A consequence side condition whose probabilities are over [atoms]. *)
Tactic Notation "gside" constr(atoms) :=
  unfold twothird, onethird, half, seventh in *;
  ptrans; pvalid; split_hyps;
  first
    [ solve [repeat split; lra]
    | match goal with Hps : pstate_admissible ?ps |- _ =>
        cells_split ps Hps atoms; cells_decide; kill_impossible; patoms_nonneg;
        repeat split; lra
      end ].

(** * Rigid formulas (the old [RigidUnchanged], [AddRigidRight],
      [AddRigidBoth]) *)

Lemma RigidUnchanged (z : ProbLogicVar) (c : Cmd) (r : R) :
  hoare_derivable (p_eq (pvar z) (pconst r)) c (p_eq (pvar z) (pconst r)).
Proof. apply HFree. cbn. tauto. Qed.

Lemma AddRigidRight (z : ProbLogicVar) (r : R) (eta1 eta2 : PFormula) (c : Cmd) :
  hoare_derivable (p_and eta1 (p_eq (pvar z) (pconst r))) c eta2 ->
  hoare_derivable (p_and eta1 (p_eq (pvar z) (pconst r))) c
    (p_and eta2 (p_eq (pvar z) (pconst r))).
Proof.
  intros H. apply HAnd; [exact H|].
  apply HConseqLeft with (pre' := p_eq (pvar z) (pconst r)); [gside (@nil CFormula)|].
  apply RigidUnchanged.
Qed.

Lemma AddRigidBoth (z : ProbLogicVar) (r : R) (eta1 eta2 : PFormula) (c : Cmd) :
  hoare_derivable eta1 c eta2 ->
  hoare_derivable (p_and eta1 (p_eq (pvar z) (pconst r))) c
    (p_and eta2 (p_eq (pvar z) (pconst r))).
Proof.
  intros H. apply HAnd.
  - apply HConseqLeft with (pre' := eta1); [|exact H].
    intros ps Hps Hp. apply psatisfies_and in Hp. tauto.
  - apply HConseqLeft with (pre' := p_eq (pvar z) (pconst r)); [|apply RigidUnchanged].
    intros ps Hps Hp. apply psatisfies_and in Hp. tauto.
Qed.

(** Side conditions of [HElimv]. *)
Ltac elimv_side := cbn; intuition discriminate.

(** * Helper theorems *)

Theorem xlt1_Else (x0 : DomProgramVar) (z1 : ProbLogicVar) :
  hoare_derivable
    {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ z1 = 1 }}
    <{ skip }>
    {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ z1 = 1 }}.
Proof. apply HSkip. Qed.

Theorem xlt1_If (x0 : DomProgramVar) (z2 : ProbLogicVar) :
  hoare_derivable
    {{ (prob true) = 0 /\ z2 = 0 }}
    (then_branch x0)
    {{ (0 = (prob (~ (x0 >= #(1%nat)))) /\ (prob true) = 0) /\ z2 = 0 }}.
Proof.
  apply AddRigidRight.
  apply HConseq with (eta1 := {{ (prob true) = 0 /\ z2 = 0 }})
                     (eta2 := {{ (prob true) = 0 /\ z2 = 0 }}).
  - gside (@nil CFormula).
  - unfold then_branch.
    apply HSeq with (eta2 := {{ (prob true) = 0 /\ z2 = 0 }}).
    + apply HConseq with (eta1 := toss_pformula b (1/3) {{ (prob true) = 0 /\ z2 = 0 }})
                         (eta2 := {{ (prob true) = 0 /\ z2 = 0 }}).
      * gside (@nil CFormula).
      * apply HBoolToss. unfold coin_probability_valid; lra.
      * gside (@nil CFormula).
    + apply HConseq with
        (eta1 := if_precondition {{ (prob true) = 0 /\ z2 = 0 }}
                                 {{ (prob true) = 0 /\ z2 = 0 }} (fvar b))
        (eta2 := {{ z2 + z2 = (prob true) /\ z2 = 0 }}).
      * gside [fvar b].
      * apply HAnd.
        -- apply HIfEq.
           ++ apply HConseq with
                (eta1 := subst_dom_pformula x0 \{ x0 + #(1%nat) \} {{ (prob true) = 0 /\ z2 = 0 }})
                (eta2 := {{ (prob true) = 0 /\ z2 = 0 }}).
              ** gside (@nil CFormula).
              ** apply HDomAssign.
              ** gside (@nil CFormula).
           ++ apply HConseq with
                (eta1 := subst_dom_pformula x0 \{ x0 - #(1%nat) \} {{ (prob true) = 0 /\ z2 = 0 }})
                (eta2 := {{ (prob true) = 0 /\ z2 = 0 }}).
              ** gside (@nil CFormula).
              ** apply HDomAssign.
              ** gside (@nil CFormula).
        -- apply HConseq with (eta1 := {{ z2 = 0 }}) (eta2 := {{ z2 = 0 }}).
           ++ gside (@nil CFormula).
           ++ apply RigidUnchanged.
           ++ gside (@nil CFormula).
      * gside (@nil CFormula).
  - gside [\{ x0 >= #(1%nat) \}].
Qed.

Theorem xlt1 (x0 : DomProgramVar) :
  hoare_derivable
    {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob true) = 1 }}.
Proof.
  apply HConseqLeft with (pre' := subst_prob_pformula y1 (PConst 1)
    {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true) }}).
  { gside (@nil CFormula). }
  apply HElimv; [|elimv_side|elimv_side].
  apply HConseqLeft with (pre' := subst_prob_pformula y2 (PConst 0)
    {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ y1 = 1 }}).
  { gside (@nil CFormula). }
  apply HElimv; [|elimv_side|elimv_side].
  apply HConseq with
    (eta1 := if_precondition {{ (prob true) = 0 /\ y2 = 0 }}
               {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true) /\ y1 = 1 }}
               \{ x0 >= #(1%nat) \})
    (eta2 := {{ (y2 + y1 = (prob (~ (x0 >= #(1%nat)))) /\ y1 = 1 /\ y2 = 0) /\
                (y2 + y1 = (prob true) /\ y1 = 1 /\ y2 = 0) }}).
  - gside [\{ x0 >= #(1%nat) \}].
  - apply HAnd.
    + apply HAnd.
      * apply HIfEq.
        -- apply HConseqRight with
             (post := {{ (0 = (prob (~ (x0 >= #(1%nat)))) /\ (prob true) = 0) /\ y2 = 0 }}).
           { gside (@nil CFormula). }
           apply xlt1_If.
        -- apply HConseq with (eta1 := {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ y1 = 1 }})
                             (eta2 := {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ y1 = 1 }}).
           ++ gside (@nil CFormula).
           ++ apply xlt1_Else.
           ++ gside (@nil CFormula).
      * apply HAnd.
        -- apply HConseqLeft with (pre' := {{ y1 = 1 }}); [gside [\{ x0 >= #(1%nat) \}]|].
           apply HFree. cbn. tauto.
        -- apply HConseqLeft with (pre' := {{ y2 = 0 }}); [gside [\{ x0 >= #(1%nat) \}]|].
           apply HFree. cbn. tauto.
    + apply HAnd.
      * apply HIfEq.
        -- apply HConseq with (eta1 := {{ (prob true) = 0 /\ y2 = 0 }})
             (eta2 := {{ (0 = (prob (~ (x0 >= #(1%nat)))) /\ (prob true) = 0) /\ y2 = 0 }}).
           ++ gside (@nil CFormula).
           ++ apply xlt1_If.
           ++ gside (@nil CFormula).
        -- apply HConseq with (eta1 := {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ y1 = 1 }})
                             (eta2 := {{ ((prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true)) /\ y1 = 1 }}).
           ++ gside (@nil CFormula).
           ++ apply xlt1_Else.
           ++ gside (@nil CFormula).
      * apply HAnd.
        -- apply HConseqLeft with (pre' := {{ y1 = 1 }}); [gside [\{ x0 >= #(1%nat) \}]|].
           apply HFree. cbn. tauto.
        -- apply HConseqLeft with (pre' := {{ y2 = 0 }}); [gside [\{ x0 >= #(1%nat) \}]|].
           apply HFree. cbn. tauto.
  - gside (@nil CFormula).
Qed.

(** The two branches of the body from [x0 = n], [n >= 1] (the old
    [ifcase], [elsecase], [ifcase2]). *)
Definition ifcase (x0 : DomProgramVar) (n : nat) : PFormula :=
  {{ ((prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true)) /\
     y1 = twothird /\ y2 = 0 /\ y3 = onethird }}.
Definition elsecase : PFormula := {{ (prob true) = 0 /\ y2 = 0 }}.
Definition ifcase2 (x0 : DomProgramVar) (n : nat) : PFormula :=
  {{ (((prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) /\ y1 = twothird /\ y2 = 0) /\
      y3 = onethird) /\ y4 = 1 }}.

Ltac unfold_cases := unfold ifcase, elsecase, ifcase2 in *.

(** [HBoolToss] for the toss in the [then] branch. *)
Lemma toss_branch (eta : PFormula) :
  hoare_derivable (toss_pformula b (1/3) {{ eta /\ (prob b) = onethird /\ (prob (~ b)) = twothird }})
    <{ b toss (1/3) }> {{ eta /\ (prob b) = onethird /\ (prob (~ b)) = twothird }}.
Proof. apply HBoolToss. unfold coin_probability_valid; lra. Qed.

(** Chain the two branches with [HIfEq]: the step used in the while proof. *)
Theorem xgeq1 (x0 : DomProgramVar) (n : nat) : (n >= 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = #((n - 1)%nat))) = twothird /\ (prob (x0 = #((n + 1)%nat))) = onethird
       /\ (prob true) = 1 }}.
Proof.
  intros Hn.
  apply HConseqRight with
    (post := {{ ((prob (x0 = #((n - 1)%nat))) = twothird /\
                 (prob (x0 = #((n + 1)%nat))) = onethird) /\ (prob true) = 1 }}).
  { gside (@nil CFormula). }
  apply HConseqLeft with (pre' := subst_prob_pformula y1 (PConst twothird)
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}).
  { gside (@nil CFormula). }
  apply HElimv; [|elimv_side|elimv_side].
  (* Main proof. *)
  apply HConseqLeft with (pre' := subst_prob_pformula y2 (PConst 0)
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) /\ y1 = twothird }}).
  { gside (@nil CFormula). }
  apply HElimv; [|elimv_side|elimv_side].
  apply HConseqLeft with (pre' := subst_prob_pformula y3 (PConst onethird)
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) /\ y1 = twothird /\ y2 = 0 }}).
  { gside (@nil CFormula). }
  apply HElimv; [|elimv_side|elimv_side].
  apply HAnd.
  - unfold GamblersRuin_Body.
    apply HConseqLeft with (pre' := if_precondition (ifcase x0 n) elsecase \{ x0 >= #(1%nat) \}).
    { unfold_cases. gconc [\{ true \}]. }
    apply HAnd.
    + (* the [n - 1] case *)
      apply HConseqRight with
        (post := {{ y1 + y2 = (prob (x0 = #((n - 1)%nat))) /\ y1 = twothird /\ y2 = 0 }}).
      { gside (@nil CFormula). }
      apply HAnd.
      * apply HIfEq.
        -- apply HSeq with (eta2 := (p_and (ifcase x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
           ++ apply HConseqLeft with (pre' := toss_pformula b (1/3)
                (p_and (ifcase x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
              { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
              apply toss_branch.
           ++ apply HConseqRight with
                (post := {{ y2 + y1 = (prob (x0 = #((n - 1)%nat))) /\ y1 = twothird /\ y2 = 0 }}).
              { gside (@nil CFormula). }
              apply HAnd.
              ** apply HConseqLeft with (pre' := if_precondition
                   {{ (prob (x0 = n)) = (prob true) /\ y2 = 0 /\ (prob b) = onethird }}
                   {{ (prob (x0 = n)) = (prob true) /\ (prob (x0 = n)) = twothird /\ y1 = twothird /\
                      (prob (~ b)) = twothird }} (fvar b)).
                 { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
                 apply HIfEq.
                 --- apply HConseqRight with (post := {{ 0 = (prob (x0 = #((n - 1)%nat))) /\ y2 = 0 }}).
                     { gside (@nil CFormula). }
                     apply HAnd.
                     +++ apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 + #(1%nat) \}
                           {{ 0 = (prob (x0 = #((n - 1)%nat))) }}).
                         { gconc [\{ true \}]. }
                         apply HDomAssign.
                     +++ apply HConseqLeft with (pre' := {{ y2 = 0 }}); [gside (@nil CFormula)|].
                         apply RigidUnchanged.
                 --- apply HConseqRight with (post := {{ twothird = (prob (x0 = #((n - 1)%nat))) /\ y1 = twothird }}).
                     { gside (@nil CFormula). }
                     apply HAnd.
                     +++ apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 - #(1%nat) \}
                           {{ twothird = (prob (x0 = #((n - 1)%nat))) }}).
                         { gconc [\{ true \}]. }
                         apply HDomAssign.
                     +++ apply HConseqLeft with (pre' := {{ y1 = twothird }}); [gside (@nil CFormula)|].
                         apply RigidUnchanged.
              ** apply HAnd.
                 --- apply HConseqLeft with (pre' := {{ y1 = twothird }}); [unfold_cases; gside (@nil CFormula)|].
                     apply RigidUnchanged.
                 --- apply HConseqLeft with (pre' := {{ y2 = 0 }}); [unfold_cases; gside (@nil CFormula)|].
                     apply RigidUnchanged.
        -- unfold elsecase. apply HConseqRight with (post := {{ (prob true) = 0 /\ y2 = 0 }}).
           { gside [\{ x0 = #((n - 1)%nat) \}]. }
           apply HSkip.
      * apply HConseqLeft with (pre' := {{ y1 = twothird /\ y2 = 0 }}); [unfold_cases; gside (@nil CFormula)|].
        apply HFree. cbn. tauto.
    + (* the [n + 1] case *)
      apply HConseqRight with
        (post := {{ y3 + y2 = (prob (x0 = #((n + 1)%nat))) /\ y3 = onethird /\ y2 = 0 }}).
      { gside (@nil CFormula). }
      apply HAnd.
      * apply HIfEq.
        -- apply HSeq with (eta2 := (p_and (ifcase x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
           ++ apply HConseqLeft with (pre' := toss_pformula b (1/3)
                (p_and (ifcase x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
              { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
              apply toss_branch.
           ++ apply HConseqRight with
                (post := {{ y3 + y2 = (prob (x0 = #((n + 1)%nat))) /\ y3 = onethird /\ y2 = 0 }}).
              { gside (@nil CFormula). }
              apply HAnd.
              ** apply HConseqLeft with (pre' := if_precondition
                   {{ (prob (x0 = n)) = (prob true) /\ (prob (x0 = n)) = onethird /\ y3 = onethird /\
                      (prob b) = onethird }}
                   {{ (prob (x0 = n)) = (prob true) /\ (prob (x0 = n)) = twothird /\ y2 = 0 /\
                      (prob (~ b)) = twothird }} (fvar b)).
                 { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
                 apply HIfEq.
                 --- apply HConseqRight with (post := {{ onethird = (prob (x0 = #((n + 1)%nat))) /\ y3 = onethird }}).
                     { gside (@nil CFormula). }
                     apply HAnd.
                     +++ apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 + #(1%nat) \}
                           {{ onethird = (prob (x0 = #((n + 1)%nat))) }}).
                         { gconc [\{ true \}]. }
                         apply HDomAssign.
                     +++ apply HConseqLeft with (pre' := {{ y3 = onethird }}); [gside (@nil CFormula)|].
                         apply RigidUnchanged.
                 --- apply HConseqRight with (post := {{ 0 = (prob (x0 = #((n + 1)%nat))) /\ y2 = 0 }}).
                     { gside (@nil CFormula). }
                     apply HAnd.
                     +++ apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 - #(1%nat) \}
                           {{ 0 = (prob (x0 = #((n + 1)%nat))) }}).
                         { gconc [\{ true \}]. }
                         apply HDomAssign.
                     +++ apply HConseqLeft with (pre' := {{ y2 = 0 }}); [gside (@nil CFormula)|].
                         apply RigidUnchanged.
              ** apply HAnd.
                 --- apply HConseqLeft with (pre' := {{ y3 = onethird }}); [unfold_cases; gside (@nil CFormula)|].
                     apply RigidUnchanged.
                 --- apply HConseqLeft with (pre' := {{ y2 = 0 }}); [unfold_cases; gside (@nil CFormula)|].
                     apply RigidUnchanged.
        -- unfold elsecase. apply HConseqRight with (post := {{ (prob true) = 0 /\ y2 = 0 }}).
           { gside [\{ x0 = #((n + 1)%nat) \}]. }
           apply HSkip.
      * apply HConseqLeft with (pre' := {{ y3 = onethird /\ y2 = 0 }}); [unfold_cases; gside (@nil CFormula)|].
        apply HFree. cbn. tauto.
  - (* total mass *)
    apply HConseqLeft with (pre' := subst_prob_pformula y4 (PConst 1)
      {{ ((prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) /\ y1 = twothird /\ y2 = 0) /\
         y3 = onethird }}).
    { gside (@nil CFormula). }
    apply HElimv; [|elimv_side|elimv_side].
    unfold GamblersRuin_Body.
    apply HConseq with (eta1 := if_precondition (ifcase2 x0 n) elsecase \{ x0 >= #(1%nat) \})
                       (eta2 := {{ ((y4 + y2 = (prob true)) /\ y4 = 1) /\ y2 = 0 }}).
    + unfold_cases. gconc [\{ true \}].
    + apply HAnd; [apply HAnd|].
      * apply HIfEq.
        -- apply HSeq with (eta2 := (p_and (ifcase2 x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
           ++ apply HConseqLeft with (pre' := toss_pformula b (1/3)
                (p_and (ifcase2 x0 n) {{ (prob b) = onethird /\ (prob (~ b)) = twothird }})).
              { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
              apply toss_branch.
           ++ apply HConseqRight with
                (post := {{ y3 + y1 = (prob true) /\ y1 = twothird /\ y3 = onethird /\ y4 = 1 }}).
              { gside (@nil CFormula). }
              apply HAnd.
              ** apply HConseqLeft with (pre' := if_precondition
                   {{ (prob true) = onethird /\ y3 = onethird }}
                   {{ (prob true) = twothird /\ y1 = twothird }} (fvar b)).
                 { unfold_cases. gconc [fvar b; \{ ~ b \}; \{ true \}]. }
                 apply HIfEq.
                 --- apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 + #(1%nat) \}
                       {{ y3 = (prob true) }}).
                     { gside (@nil CFormula). }
                     apply HDomAssign.
                 --- apply HConseqLeft with (pre' := subst_dom_pformula x0 \{ x0 - #(1%nat) \}
                       {{ y1 = (prob true) }}).
                     { gside (@nil CFormula). }
                     apply HDomAssign.
              ** apply HAnd.
                 --- apply HConseqLeft with (pre' := {{ y1 = twothird }}); [unfold_cases; gside (@nil CFormula)|].
                     apply RigidUnchanged.
                 --- apply HAnd.
                     +++ apply HConseqLeft with (pre' := {{ y3 = onethird }}); [unfold_cases; gside (@nil CFormula)|].
                         apply RigidUnchanged.
                     +++ apply HConseqLeft with (pre' := {{ y4 = 1 }}); [unfold_cases; gside (@nil CFormula)|].
                         apply RigidUnchanged.
        -- unfold elsecase. apply HConseqLeft with (pre' := {{ y2 = (prob true) }}).
           { gside (@nil CFormula). }
           apply HSkip.
      * apply HConseqLeft with (pre' := {{ y4 = 1 }}); [unfold_cases; gside (@nil CFormula)|].
        apply RigidUnchanged.
      * apply HConseqLeft with (pre' := {{ y2 = 0 }}); [unfold_cases; gside (@nil CFormula)|].
        apply RigidUnchanged.
    + gside (@nil CFormula).
Qed.
(** The postcondition of [xgeq1], used as the intermediate assertion of
    the consequence steps below (as in the old proofs). *)
Notation xgeq1_post x0 n :=
  {{ (prob (x0 = #((n - 1)%nat))) = twothird /\ (prob (x0 = #((n + 1)%nat))) = onethird
     /\ (prob true) = 1 }} (only parsing).

Theorem xgeq1_m (x0 : DomProgramVar) (n : nat) : (n >= 1)%nat ->
  forall m : nat, neqnat m (n - 1) -> neqnat m (n + 1) ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = m)) = 0 }}.
Proof.
  unfold neqnat. intros Hn m H1 H2.
  apply HConseqRight with (post := xgeq1_post x0 n).
  - gext [\{ x0 = #((n - 1)%nat) \}; \{ x0 = #((n + 1)%nat) \}; \{ x0 = m \}; \{ true \}].
    pose proof (Pr_sum3_le ps \{ x0 = #((n - 1)%nat) \} \{ x0 = #((n + 1)%nat) \} \{ x0 = m \} Hps
                  ltac:(cfast_quick) ltac:(cfast_quick) ltac:(cfast_quick)).
    pose proof (Pr_nonneg ps \{ x0 = m \}). unfold Pc in *. lra.
  - apply xgeq1. exact Hn.
Qed.

Theorem xgeq1_m_UB (x0 : DomProgramVar) (n m : nat) :
  (n >= 1)%nat -> neqnat m (n - 1) -> neqnat m (n + 1) ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = m)) <= 0 }}.
Proof.
  intros Hn H1 H2.
  apply HConseqRight with (post := {{ (prob (x0 = m)) = 0 }}).
  - gside (@nil CFormula).
  - apply xgeq1_m; assumption.
Qed.

Theorem xgeq1_m_UB2 (x0 : DomProgramVar) (n m : nat) :
  (n >= 1)%nat -> (m > n + 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 >= m)) = 0 }}.
Proof.
  intros Hn Hm.
  apply HConseqRight with (post := xgeq1_post x0 n).
  - gext [\{ x0 = #((n - 1)%nat) \}; \{ x0 = #((n + 1)%nat) \}; \{ x0 >= m \}; \{ true \}].
    pose proof (Pr_sum3_le ps \{ x0 = #((n - 1)%nat) \} \{ x0 = #((n + 1)%nat) \} \{ x0 >= m \} Hps
                  ltac:(cfast_quick) ltac:(cfast_quick) ltac:(cfast_quick)).
    pose proof (Pr_nonneg ps \{ x0 >= m \}). unfold Pc in *. lra.
  - apply xgeq1. exact Hn.
Qed.

Theorem xgeq1_n_UB (x0 : DomProgramVar) (n : nat) : (n >= 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = #((n - 1)%nat))) <= twothird }} /\
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = n)) <= 0 }} /\
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = #((n + 1)%nat))) <= onethird }}.
Proof.
  intros Hn. split; [|split].
  - apply HConseqRight with (post := xgeq1_post x0 n).
    { gside (@nil CFormula). }
    apply HAnd.
    + apply HConseqRight with (post := xgeq1_post x0 n); [gside (@nil CFormula)|].
      apply xgeq1. exact Hn.
    + apply HConseqRight with (post := xgeq1_post x0 n); [gside (@nil CFormula)|].
      apply xgeq1. exact Hn.
  - apply (xgeq1_m_UB x0 n n); [exact Hn | unfold neqnat; lia | unfold neqnat; lia].
  - apply HConseqRight with (post := xgeq1_post x0 n).
    { gside (@nil CFormula). }
    apply HAnd.
    + apply HConseqRight with (post := xgeq1_post x0 n); [gside (@nil CFormula)|].
      apply xgeq1. exact Hn.
    + apply HConseqRight with (post := xgeq1_post x0 n); [gside (@nil CFormula)|].
      apply xgeq1. exact Hn.
Qed.

Theorem xeq1_UB (x0 : DomProgramVar) :
  hoare_derivable
    {{ (prob (x0 = #(1%nat))) = 1 /\ (prob (x0 = #(1%nat))) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (~ (x0 >= #(1%nat)))) <= twothird }} /\
  hoare_derivable
    {{ (prob (x0 = #(1%nat))) = 1 /\ (prob (x0 = #(1%nat))) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = #(1%nat))) <= 0 }} /\
  hoare_derivable
    {{ (prob (x0 = #(1%nat))) = 1 /\ (prob (x0 = #(1%nat))) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 = #(2%nat))) <= onethird }}.
Proof.
  split.
  - apply HConseqRight with
      (post := {{ (prob (x0 = #(0%nat))) = twothird /\ (prob (x0 = #(2%nat))) = onethird /\
                  (prob true) = 1 }}).
    + gext [\{ x0 = #(0%nat) \}; \{ x0 = #(2%nat) \}; \{ true \}]. unfold Pc in *. lra.
    + apply (xgeq1 x0 1). lia.
  - exact (proj2 (xgeq1_n_UB x0 1 ltac:(lia))).
Qed.

Theorem xgeq1_lt1_UB (x0 : DomProgramVar) (n : nat) : (n > 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (~ (x0 >= #(1%nat)))) <= 0 }}.
Proof.
  intros Hn.
  apply HConseqRight with (post := {{ (prob (x0 = #(0%nat))) = 0 }}).
  - gext [\{ x0 = #(0%nat) \}]. unfold Pc in *. lra.
  - apply (xgeq1_m x0 n); [lia | unfold neqnat; lia | unfold neqnat; lia].
Qed.

Theorem xgeq1_max (x0 : DomProgramVar) (n : nat) : (n >= 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (x0 >= #((n + 1)%nat))) = onethird }}.
Proof.
  intros Hn.
  apply HConseqRight with
    (post := {{ (prob (x0 = #((n + 1)%nat))) = onethird /\ (prob (x0 >= #((n + 2)%nat))) = 0 }}).
  - gext [\{ x0 = #((n + 1)%nat) \}; \{ x0 >= #((n + 2)%nat) \}; \{ x0 >= #((n + 1)%nat) \}].
    pose proof (Pr_sum2 ps \{ x0 = #((n + 1)%nat) \} \{ x0 >= #((n + 2)%nat) \}
                  \{ x0 >= #((n + 1)%nat) \} Hps ltac:(cfast_quick) ltac:(cfast_quick)).
    unfold Pc in *. lra.
  - apply HAnd.
    + apply HConseqRight with (post := xgeq1_post x0 n); [gside (@nil CFormula)|].
      apply xgeq1. exact Hn.
    + apply (xgeq1_m_UB2 x0 n (n + 2)); lia.
Qed.

Theorem xgeq_max_UB (x0 : DomProgramVar) (n : nat) : (n >= 1)%nat ->
  hoare_derivable
    {{ (prob (x0 = n)) = 1 /\ (prob (x0 = n)) = (prob true) }}
    (GamblersRuin_Body x0)
    {{ (prob (~ ~ (x0 >= #((n + 1)%nat)) /\ (x0 >= #((n + 1)%nat)))) <= onethird }}.
Proof.
  intros Hn.
  apply HConseqRight with (post := {{ (prob (x0 >= #((n + 1)%nat))) = onethird }}).
  - gext [\{ x0 >= #((n + 1)%nat) \}]. unfold Pc in *. lra.
  - apply xgeq1_max. exact Hn.
Qed.

(** [/\_{i = 1..max} Pr(x0 = i) <= 0]. *)
Fixpoint xlt1_1ton (max : nat) (x0 : DomProgramVar) : PFormula :=
  match max with
  | O => p_true
  | S m => p_and (xlt1_1ton m x0) {{ (prob (x0 = #(S m))) <= 0 }}
  end.

(** With no mass on [x0 >= 1], every [Pr(x0 = i)] with [i >= 1] is 0 (the
    induction in the old [xlt1_ant] side condition). *)
Lemma xlt1_1ton_valid (x0 : DomProgramVar) (m : nat) (ps : Pstate) :
  pstate_admissible ps -> Pr[ps] \{ x0 >= #(1%nat) \} = 0 -> psatisfies ps (xlt1_1ton m x0).
Proof.
  intros Hps H0. induction m as [|m IH]; cbn [xlt1_1ton].
  - apply psatisfies_true.
  - apply psatisfies_and. split; [exact IH|]. apply psatisfies_le. cbn [pterm_eval].
    rewrite <- H0. apply Pr_mono; [exact Hps|]. cfast.
Qed.

(** The antecedent of the while rule for the region [x0 < 1]. *)
Theorem xlt1_ant (n : nat) (x0 : DomProgramVar) : (n >= 1)%nat ->
  hoare_derivable
    {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true) }}
    (GamblersRuin_Body x0)
    (p_and (p_and {{ (prob (~ (x0 >= #(1%nat)))) <= 1 }} (xlt1_1ton (n - 1) x0))
           {{ (prob (~ ~ (x0 >= n) /\ (x0 >= n))) <= 0 }}).
Proof.
  intros Hn.
  apply HConseqRight with (post := {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob true) = 1 }}).
  - intros ps Hps H. apply psatisfies_and in H as [H1 H2].
    apply psatisfies_eq in H1, H2. cbn [pterm_eval] in H1, H2. unfold pconst in *.
    cbn [pterm_eval] in H1, H2.
    assert (Hge : Pr[ps] \{ x0 >= #(1%nat) \} = 0).
    { match type of H1 with Pr[ps] ?a = _ => match type of H2 with Pr[ps] ?t = _ =>
        pose proof (Pr_sum2 ps \{ x0 >= #(1%nat) \} a t Hps ltac:(cfast_quick) ltac:(cfast_quick))
      end end.
      pose proof (Pr_nonneg ps \{ x0 >= #(1%nat) \}). lra. }
    apply psatisfies_and. split; [apply psatisfies_and; split|].
    + apply psatisfies_le. cbn [pterm_eval]. unfold pconst. cbn [pterm_eval]. lra.
    + apply xlt1_1ton_valid; assumption.
    + apply psatisfies_le. cbn [pterm_eval]. unfold pconst. cbn [pterm_eval].
      rewrite <- Hge. apply Pr_mono; [exact Hps|]. cfast.
  - apply xlt1.
Qed.

(** * The while rule *)

(** Regions [x0 < 1], [x0 = 1], ..., [x0 = max] (the old [Gs max x0]). *)
Definition Gs (x0 : DomProgramVar) (i : nat) : CFormula :=
  match i with
  | O => \{ ~ (x0 >= #(1%nat)) \}
  | S _ => \{ x0 = i \}
  end.

(** Transitions (the old [Ps max]): region 0 stays put; region [i >= 1]
    moves down with 2/3 and up with 1/3 (if still a region). *)
Definition Ps (max i j : nat) : R :=
  match i with
  | O => if Nat.eqb j 0 then 1 else 0
  | S _ => if Nat.eqb j (i - 1) then 2/3
           else if andb (Nat.eqb j (i + 1)) (Nat.leb j max) then 1/3 else 0
  end.

(** Exits (the old [Ts (S max)]): 1/3 from the top region, 0 elsewhere. *)
Definition Ts (max i : nat) : R := if Nat.eqb i max then 1/3 else 0.

Definition GamblersRuin (max : nat) : Cmd :=
  CWhile \{ ~ (x >= max) \} (GamblersRuin_Body x).

(** TPHL's body postcondition [finite_p_and 3 f /\ exit] nests to the left
    with a leading [p_true]; the old vectors nested to the right.  Each case
    of [ant_1to3] first steps to the old (right-nested) shape. *)
Ltac reshape_side :=
  intros ps Hps H; unfold while_body_post_upper, Gs, Ps, Ts in *;
  cbn [finite_p_and Nat.eqb Nat.leb Nat.sub Nat.add andb] in *;
  repeat rewrite psatisfies_and in *; split_hyps;
  repeat split; try apply psatisfies_true; try assumption;
  rewrite psatisfies_le in *; cbn [pterm_eval] in *; unfold pconst in *; cbn [pterm_eval] in *;
  lra.

Theorem ant_1to3 (x0 : DomProgramVar) : forall i, (i < 3)%nat ->
  hoare_derivable (p_concentrated_unit (Gs x0 i)) (GamblersRuin_Body x0)
    (while_body_post_upper 3 (Gs x0) (Ps 2 i) \{ ~ (x0 >= #(3%nat)) \}
                           \{ x0 >= #(3%nat) \} (Ts 2 i)).
Proof.
  intros i Hi. destruct i as [|[|[|i]]]; [| | |lia].
  - apply HConseqLeft with
      (pre' := {{ (prob (~ (x0 >= #(1%nat)))) = 1 /\ (prob (~ (x0 >= #(1%nat)))) = (prob true) }}).
    { unfold Gs. gside (@nil CFormula). }
    apply HConseqRight with
      (post := p_and (p_and {{ (prob (~ (x0 >= #(1%nat)))) <= 1 }} (xlt1_1ton 2 x0))
                     {{ (prob (~ ~ (x0 >= #(3%nat)) /\ (x0 >= #(3%nat)))) <= 0 }}).
    { unfold while_body_post_upper, Gs, Ps, Ts. cbn [xlt1_1ton].
      gext [\{ ~ (x0 >= #(1%nat)) \}; \{ x0 = #(1%nat) \}; \{ x0 = #(2%nat) \}; \{ x0 >= #(3%nat) \}; \{ true \}].
      unfold Pc in *. cbn [Nat.eqb Nat.leb andb Nat.sub Nat.add] in *. repeat split; try exact I; lra. }
    apply (xlt1_ant 3 x0). lia.
  - apply HConseqLeft with
      (pre' := {{ (prob (x0 = #(1%nat))) = 1 /\ (prob (x0 = #(1%nat))) = (prob true) }}).
    { unfold Gs. gside (@nil CFormula). }
    apply HConseqRight with
      (post := p_and
         (p_and {{ (prob (~ (x0 >= #(1%nat)))) <= twothird }}
                (p_and {{ (prob (x0 = #(1%nat))) <= 0 }} {{ (prob (x0 = #(2%nat))) <= onethird }}))
         {{ (prob (x0 >= #(3%nat))) = 0 }}).
    { unfold while_body_post_upper, Gs, Ps, Ts, twothird, onethird. cbn [finite_p_and Nat.eqb Nat.leb Nat.sub Nat.add andb].
      gext [\{ ~ (x0 >= #(1%nat)) \}; \{ x0 = #(1%nat) \}; \{ x0 = #(2%nat) \}; \{ x0 >= #(3%nat) \}; \{ true \}].
      unfold Pc in *. cbn [Nat.eqb Nat.leb andb Nat.sub Nat.add] in *. repeat split; try exact I; lra. }
    apply HAnd.
    + apply HAnd.
      * exact (proj1 (xeq1_UB x0)).
      * apply HAnd.
        -- apply (xgeq1_m_UB x0 1 1); [lia | unfold neqnat; lia | unfold neqnat; lia].
        -- apply HConseqRight with (post := {{ (prob (x0 = #(2%nat))) <= onethird }}).
           { gside (@nil CFormula). }
           exact (proj2 (proj2 (xgeq1_n_UB x0 1 ltac:(lia)))).
    + apply HConseqRight with (post := {{ (prob (x0 >= #(3%nat))) = 0 }}).
      { gside (@nil CFormula). }
      apply (xgeq1_m_UB2 x0 1 3); lia.
  - apply HConseqLeft with
      (pre' := {{ (prob (x0 = #(2%nat))) = 1 /\ (prob (x0 = #(2%nat))) = (prob true) }}).
    { unfold Gs. gside (@nil CFormula). }
    apply HConseqRight with
      (post := p_and
         (p_and {{ (prob (~ (x0 >= #(1%nat)))) <= 0 }}
                (p_and {{ (prob (x0 = #(1%nat))) <= twothird }} {{ (prob (x0 = #(2%nat))) <= 0 }}))
         {{ (prob (~ ~ (x0 >= #(3%nat)) /\ (x0 >= #(3%nat)))) <= onethird }}).
    { unfold while_body_post_upper, Gs, Ps, Ts, twothird, onethird. cbn [finite_p_and Nat.eqb Nat.leb Nat.sub Nat.add andb].
      gext [\{ ~ (x0 >= #(1%nat)) \}; \{ x0 = #(1%nat) \}; \{ x0 = #(2%nat) \}; \{ x0 >= #(3%nat) \}; \{ true \}].
      unfold Pc in *. cbn [Nat.eqb Nat.leb andb Nat.sub Nat.add] in *. repeat split; try exact I; lra. }
    apply HAnd.
    + apply HAnd.
      * apply (xgeq1_lt1_UB x0 2). lia.
      * apply HAnd.
        -- exact (proj1 (xgeq1_n_UB x0 2 ltac:(lia))).
        -- apply HConseqRight with (post := {{ (prob (x0 = #(2%nat))) <= 0 }}).
           { gside (@nil CFormula). }
           exact (proj1 (proj2 (xgeq1_n_UB x0 2 ltac:(lia)))).
    + apply (xgeq_max_UB x0 2). lia.
Qed.

(** Gambler's ruin from 1 with goal 3: [x_i = (2^i - 1)/(2^N - 1)], so
    [x_1 = 1/7] and [x_2 = 3/7]. *)
Definition solution (i : nat) : R :=
  match i with O => 0 | 1 => 1/7 | _ => 3/7 end.

Theorem Gambler3_UB :
  hoare_derivable
    {{ (prob (x = #(1%nat))) = y /\ (prob (x = #(1%nat))) = (prob true) /\ y = 1 }}
    (GamblersRuin 3)
    {{ (prob (x >= #(3%nat))) <= seventh }}.
Proof.
  apply HConseq with
    (eta1 := p_and (p_and (p_almost_sure (c_and \{ ~ (x >= #(3%nat)) \} (Gs x 1)))
                          (PFLe (PProb c_true) (PVar y)))
                   {{ y = 1 }})
    (eta2 := p_and (PFLe (PProb \{ x >= #(3%nat) \}) (PMul (PConst (solution 1)) (PVar y)))
                   {{ y = 1 }}).
  - unfold Gs. gext [\{ x = #(1%nat) \}; \{ true \}]. unfold Pc in *. repeat split; lra.
  - apply AddRigidBoth. unfold GamblersRuin.
    apply (HWhileUpper 3 1 \{ ~ (x >= #(3%nat)) \} \{ x >= #(3%nat) \}
             (GamblersRuin_Body x) (Gs x) solution (Ts 2) (Ps 2) y).
    + lia.
    + while_side. unfold Gs. cfast.
    + apply ant_1to3.
    + while_side. below_cases; unfold solution, Ps, Ts; cbn [Nat.eqb Nat.leb Nat.sub Nat.add andb];
        lra.
  - unfold seventh, solution. gside (@nil CFormula).
Qed.

End GamblersRuin.
