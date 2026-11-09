(** Conditional samples.

    [z := toss(1/2); if z then (x := toss(p); y := toss(p))
                          else (x := toss(q); y := toss(q))].
    Given [z], the samples [x] and [y] are independent.

    A toss rate outside [0,1] denotes the zero kernel, so every lemma that
    tosses with [p] (resp. [q]) assumes [0 <= p <= 1] (resp. [0 <= q <= 1]);
    this also discharges [HBoolToss]'s premise [coin_probability_valid].

    Tosses and assignments are [HConseqLeft] onto [toss_pformula] /
    [subst_bool_pformula] and the leaf rule; ifs are [HConseqLeft] onto
    [if_precondition] and [HIfEq]; logic variables are removed with
    [eliminate_y] (below).  In the [_int] proofs a branch postcondition
    [Pr(G) = y] is turned into [y = Pr(G)] by an [HConseqRight] step.  Side
    conditions are proved by [cs_side]/[indep_side]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms Soundness.AssertionFacts.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

(** A real constant inside a probabilistic formula. *)
Notation "'#(' x ')'" := (pconst x) (in custom tpf at level 0, x constr at level 200)
  : tphl_scope.

Module CondSamples.

Notation x := (bool_program_var "x").
Notation y := (bool_program_var "y").
Notation z := (bool_program_var "z").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").

Definition CondSamples (p q : R) : Cmd :=
  <{ z toss 0.5;
     if z then x toss p; y toss p else x toss q; y toss q end }>.


(** Substitute the values fixed by the hypotheses: probabilistic logic
    variables, and atom probabilities pinned to a constant. *)
Ltac cs_subst :=
  repeat match goal with
  | H : pstate_prob_logic_values ?ps ?v = ?e |- _ => rewrite H in *; clear H
  | H : ?e = pstate_prob_logic_values ?ps ?v |- _ => rewrite <- H in *; clear H
  end;
  repeat match goal with
  | H : ?l = ?r |- _ =>
      match l with
      | context [Patom ?ps ?L] =>
          let E := fresh in assert (E : Patom ps L = r) by lra; rewrite E in *; clear E H
      end
  end.

Ltac cs_auto :=
  ptrans; pvalid; patoms [fvar z]; cs_subst; first [ring | lra | nra].

(** Side conditions of the rule steps: [cs_auto], or atomize on all three
    variables. *)
Ltac cs_side :=
  first [ cs_auto
        | ptrans; pvalid; patoms [fvar x; fvar y; fvar z]; cs_subst; first [ring | lra | nra] ].

(** [eliminate_y]: from
    [{eta1 /\ y = r} c {eta2}] derive [{eta1[y := r]} c {eta2[y := r]}].
    Derived from [HInstantiate] (ELIMV, FREE, AND) and CONS. *)
Lemma eliminate_y (eta1 eta2 : PFormula) (v : ProbLogicVar) (r : R) (c : Cmd) :
  hoare_derivable (p_and eta1 (p_eq (PVar v) (PConst r))) c eta2 ->
  hoare_derivable (subst_prob_pformula v (PConst r) eta1) c (subst_prob_pformula v (PConst r) eta2).
Proof.
  intros H. apply (HInstantiate v r) in H. eapply HConseqLeft; [|exact H].
  assert (E : subst_prob_pformula v (PConst r) (p_and eta1 (p_eq (PVar v) (PConst r)))
              = p_and (subst_prob_pformula v (PConst r) eta1) (p_eq (PConst r) (PConst r))).
  { unfold p_eq, p_and, p_not. cbn [subst_prob_pformula subst_prob_pterm].
    destruct (prob_logic_var_eq_dec v v) as [_|Hne]; [reflexivity|congruence]. }
  rewrite E. intros ps Hps. rewrite psatisfies_impl. intros Hp.
  apply psatisfies_and. split; [exact Hp|]. apply psatisfies_eq. reflexivity.
Qed.

(** [eliminate_y] for a closed term [p] with value [r] (e.g. [y = 0.5 * q]). *)
Lemma eliminate_y_term (eta1 eta2 : PFormula) (v : ProbLogicVar) (p : Pterm) (r : R) (c : Cmd) :
  (forall ps, pterm_eval p ps = r) ->
  hoare_derivable (p_and eta1 (p_eq (PVar v) p)) c eta2 ->
  hoare_derivable (subst_prob_pformula v (PConst r) eta1) c (subst_prob_pformula v (PConst r) eta2).
Proof.
  intros Hp H. apply eliminate_y. eapply HConseqLeft; [|exact H].
  intros ps Hps. rewrite psatisfies_impl. intros Hq.
  apply psatisfies_and in Hq as [H1 H2]. apply psatisfies_and. split; [exact H1|].
  apply psatisfies_eq in H2. apply psatisfies_eq. cbn [pterm_eval] in *. rewrite Hp. exact H2.
Qed.

(** Combine the four facts of [if_then_indep]. *)
Ltac indep_side :=
  ptrans; pvalid; split_hyps;
  repeat match goal with
  | H : ?c = Pr[?ps] ?g |- _ => rewrite <- H in *; clear H
  end;
  ring.

Lemma z_true_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 }}
    <{ x toss p; y toss p }> {{ (prob (z <-> true)) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob (z <-> true)) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob (z <-> true)) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob (z <-> true)) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob (z <-> true)) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob (z <-> true)) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob (z <-> true)) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob (z <-> true)) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma z_true_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob (z <-> true)) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply z_true_2; assumption]. cs_side.
Qed.

Lemma z_true (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 = (prob (z <-> true)) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5)) {{ y1 + 0 = (prob (z <-> true)) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob (z <-> true)) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (z_true_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob (z <-> false)) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob (z <-> false)) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob (z <-> false)) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob (z <-> false)) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma z_false_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 }}
    <{ x toss q; y toss q }> {{ (prob (z <-> false)) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob (z <-> false)) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob (z <-> false)) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob (z <-> false)) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma z_false_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob (z <-> false)) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply z_false_2; assumption]. cs_side.
Qed.

Lemma z_false (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 = (prob (z <-> false)) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 = (prob (z <-> false)) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5)) {{ y1 + y2 = (prob (z <-> false)) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (z_false_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_z_true_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (z <-> true))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> true) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob ((x <-> true) /\ (z <-> true))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob ((x <-> true) /\ (z <-> true))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> true) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob ((x <-> true) /\ (z <-> true))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob ((x <-> true) /\ (z <-> true))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_z_true_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_z_true_2; assumption]. cs_side.
Qed.

Lemma x_true_z_true (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * p = (prob ((x <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * p)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * p)) {{ y1 + 0 = (prob ((x <-> true) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> true) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_z_true_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_z_true_1 (p t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (z <-> true))) = y1 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := {{ (prob ((x <-> false) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob ((x <-> false) /\ (z <-> true))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob ((x <-> false) /\ (z <-> true))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> false) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob ((x <-> false) /\ (z <-> true))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob ((x <-> false) /\ (z <-> true))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_z_true_int (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_z_true_2; assumption]. cs_side.
Qed.

Lemma x_false_z_true (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t = (prob ((x <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * t)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * t)) {{ y1 + 0 = (prob ((x <-> false) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> false) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_z_true_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma y_true_z_true_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p }}
    <{ x toss p; y toss p }> {{ (prob ((y <-> true) /\ (z <-> true))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((y <-> true) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((y <-> true) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_true_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((y <-> true) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((y <-> true) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((y <-> true) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_true_z_true_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply y_true_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply y_true_z_true_2; assumption]. cs_side.
Qed.

Lemma y_true_z_true (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * p = (prob ((y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * p)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * p)) {{ y1 + 0 = (prob ((y <-> true) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((y <-> true) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (y_true_z_true_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma y_false_z_true_1 (p t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t }}
    <{ x toss p; y toss p }> {{ (prob ((y <-> false) /\ (z <-> true))) = y1 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((y <-> false) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((y <-> false) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_false_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((y <-> false) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((y <-> false) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((y <-> false) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_false_z_true_int (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply y_false_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply y_false_z_true_2; assumption]. cs_side.
Qed.

Lemma y_false_z_true (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t = (prob ((y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * t)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * t)) {{ y1 + 0 = (prob ((y <-> false) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((y <-> false) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (y_false_z_true_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> true) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob ((x <-> true) /\ (z <-> false))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob ((x <-> true) /\ (z <-> false))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_z_false_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (z <-> false))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> true) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob ((x <-> true) /\ (z <-> false))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob ((x <-> true) /\ (z <-> false))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_z_false_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * q }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_z_false_2; assumption]. cs_side.
Qed.

Lemma x_true_z_false (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * q = (prob ((x <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * q = (prob ((x <-> true) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * q)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * q)) {{ y1 + y2 = (prob ((x <-> true) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_z_false_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := {{ (prob ((x <-> false) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p {{ (prob ((x <-> false) /\ (z <-> false))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y p {{ (prob ((x <-> false) /\ (z <-> false))) = y1 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_z_false_2 (q t : R) (Ht : t = 1 - q) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (z <-> false))) = y2 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := {{ (prob ((x <-> false) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q {{ (prob ((x <-> false) /\ (z <-> false))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := toss_pformula y q {{ (prob ((x <-> false) /\ (z <-> false))) = y2 }}).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_z_false_int (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * t }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_z_false_2; assumption]. cs_side.
Qed.

Lemma x_false_z_false (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t = (prob ((x <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * t = (prob ((x <-> false) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * t)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * t)) {{ y1 + y2 = (prob ((x <-> false) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_z_false_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma y_true_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((y <-> true) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((y <-> true) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((y <-> true) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_true_z_false_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q }}
    <{ x toss q; y toss q }> {{ (prob ((y <-> true) /\ (z <-> false))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((y <-> true) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((y <-> true) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_true_z_false_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * q }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply y_true_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply y_true_z_false_2; assumption]. cs_side.
Qed.

Lemma y_true_z_false (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * q = (prob ((y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * q = (prob ((y <-> true) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * q)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * q)) {{ y1 + y2 = (prob ((y <-> true) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (y_true_z_false_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma y_false_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((y <-> false) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((y <-> false) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((y <-> false) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_false_z_false_2 (q t : R) (Ht : t = 1 - q) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t }}
    <{ x toss q; y toss q }> {{ (prob ((y <-> false) /\ (z <-> false))) = y2 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((y <-> false) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((y <-> false) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma y_false_z_false_int (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * t }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply y_false_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply y_false_z_false_2; assumption]. cs_side.
Qed.

Lemma y_false_z_false (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t = (prob ((y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * t = (prob ((y <-> false) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * t)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * t)) {{ y1 + y2 = (prob ((y <-> false) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (y_false_z_false_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_y_true_z_true_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p * p }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_true_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_true_z_true_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p * p)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p * p }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_y_true_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_y_true_z_true_2; assumption]. cs_side.
Qed.

Lemma x_true_y_true_z_true (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * p * p = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * p * p)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * p * p)) {{ y1 + 0 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p * p }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_y_true_z_true_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_y_false_z_true_1 (p t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p * t }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_false_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_false_z_true_int (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p * t)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * p * t }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_y_false_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_y_false_z_true_2; assumption]. cs_side.
Qed.

Lemma x_true_y_false_z_true (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * p * t = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * p * t)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * p * t)) {{ y1 + 0 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * p * t }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_y_false_z_true_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_y_false_z_true_1 (p t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t * t }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_false_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_false_z_true_int (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t * t)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t * t }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_y_false_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_y_false_z_true_2; assumption]. cs_side.
Qed.

Lemma x_false_y_false_z_true (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t * t = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * t * t)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * t * t)) {{ y1 + 0 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t * t }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_y_false_z_true_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_y_true_z_true_1 (p t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t * p }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_true_z_true_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0 /\ y2 = 0 }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_true_z_true_int (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t * p)
       /\ y2 = 0 }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> true)) = 0.5 /\ y1 = 0.5 * t * p }}
      {{ (prob (z <-> true)) = 0 /\ y2 = 0 }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_y_true_z_true_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_y_true_z_true_2; assumption]. cs_side.
Qed.

Lemma x_false_y_true_z_true (p q t : R) (Ht : t = 1 - p) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> true)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t * p = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0.5 * t * p)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 }})
      (eta2 := subst_prob_pformula y1 (PConst (0.5 * t * p)) {{ y1 + 0 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0)) {{ (prob ((z <-> true) /\ z)) = 0.5 /\ (prob ((z <-> true) /\ ~ z)) = 0 /\ y1 = 0.5 * t * p }})
        (eta2 := subst_prob_pformula y2 (PConst (0)) {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_y_true_z_true_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_y_true_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_true_z_false_2 (q : R) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q * q }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y2 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_true_z_false_int (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * q * q }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q * q }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_y_true_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_y_true_z_false_2; assumption]. cs_side.
Qed.

Lemma x_true_y_true_z_false (p q : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * q * q = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * q * q = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * q * q)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * q * q)) {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_y_true_z_false_int p q Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_true_y_false_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_false_z_false_2 (q t : R) (Ht : t = 1 - q) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q * t }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y2 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_true_y_false_z_false_int (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * q * t }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * q * t }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_true_y_false_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_true_y_false_z_false_2; assumption]. cs_side.
Qed.

Lemma x_true_y_false_z_false (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * q * t = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * q * t = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * q * t)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * q * t)) {{ y1 + y2 = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_true_y_false_z_false_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_y_false_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_false_z_false_2 (q t : R) (Ht : t = 1 - q) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t * t }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y2 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_false_z_false_int (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * t * t }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t * t }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_y_false_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_y_false_z_false_2; assumption]. cs_side.
Qed.

Lemma x_false_y_false_z_false (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t * t = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * t * t = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * t * t)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * t * t)) {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_y_false_z_false_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Lemma x_false_y_true_z_false_1 (p : R) (Hp0 : 0 <= p) (Hp1 : p <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
    <{ x toss p; y toss p }> {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y1 }}.
Proof.
  intros.
  apply HSeq with (eta2 := toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y1 }}).
  - apply HConseqLeft with (pre' := toss_pformula x p (toss_pformula y p {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y1 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_true_z_false_2 (q t : R) (Ht : t = 1 - q) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t * q }}
    <{ x toss q; y toss q }> {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y2 }}.
Proof.
  intros. subst.
  apply HSeq with (eta2 := toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y2 }}).
  - apply HConseqLeft with (pre' := toss_pformula x q (toss_pformula y q {{ (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) = y2 }})).
    + cs_side.
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Lemma x_false_y_true_z_false_int (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable
    {{ ((prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0)
       /\ y2 = 0.5 * t * q }}
    <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := if_precondition
      {{ (prob (z <-> false)) = 0 /\ y1 = 0 }}
      {{ (prob (z <-> false)) = 0.5 /\ y2 = 0.5 * t * q }} \{ z \}).
  - cs_side.
  - apply HIfEq.
    + eapply HConseqRight; [|apply x_false_y_true_z_false_1; assumption]. cs_side.
    + eapply HConseqRight; [|apply x_false_y_true_z_false_2; assumption]. cs_side.
Qed.

Lemma x_false_y_true_z_false (p q t : R) (Ht : t = 1 - q) (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> false)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> {{ 0.5 * t * q = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) }}.
Proof.
  intros. apply HConseqLeft with (pre' := {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }}).
  - cs_side.
  - apply HConseq with
      (eta1 := subst_prob_pformula y1 (PConst (0)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 }})
      (eta2 := subst_prob_pformula y1 (PConst (0)) {{ y1 + 0.5 * t * q = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) }}).
    + cs_side.
    + apply eliminate_y. apply HConseq with
        (eta1 := subst_prob_pformula y2 (PConst (0.5 * t * q)) {{ (prob ((z <-> false) /\ z)) = 0 /\ (prob ((z <-> false) /\ ~ z)) = 0.5 /\ y1 = 0 }})
        (eta2 := subst_prob_pformula y2 (PConst (0.5 * t * q)) {{ y1 + y2 = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false))) }}).
      * cs_side.
      * eapply eliminate_y_term; [|apply (x_false_y_true_z_false_int p q t Ht Hp0 Hp1 Hq0 Hq1)]. intros; cbn; ring.
      * cs_side.
    + cs_side.
Qed.

Definition post_cond (X Y Z : bool) : PFormula :=
  {{ (prob (z <-> Z)) * (prob ((x <-> X) /\ (y <-> Y) /\ (z <-> Z)))
     = (prob ((x <-> X) /\ (z <-> Z))) * (prob ((y <-> Y) /\ (z <-> Z))) }}.

Theorem if_then_indep (X Y Z : bool) (p q : R)
  (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob (z <-> Z)) = 0.5 }} <{ if z then x toss p; y toss p else x toss q; y toss q end }> (post_cond X Y Z).
Proof.
  unfold post_cond. destruct X, Y, Z.
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> true))) /\
                     (0.5 * p * p = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> true)))) /\
                     (0.5 * p = (prob ((x <-> true) /\ (z <-> true)))) /\
                     (0.5 * p = (prob ((y <-> true) /\ (z <-> true)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_true p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_true_y_true_z_true p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_true_z_true p q Hp0 Hp1 Hq0 Hq1)|apply (y_true_z_true p q Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> false))) /\
                     (0.5 * q * q = (prob ((x <-> true) /\ (y <-> true) /\ (z <-> false)))) /\
                     (0.5 * q = (prob ((x <-> true) /\ (z <-> false)))) /\
                     (0.5 * q = (prob ((y <-> true) /\ (z <-> false)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_false p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_true_y_true_z_false p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_true_z_false p q Hp0 Hp1 Hq0 Hq1)|apply (y_true_z_false p q Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> true))) /\
                     (0.5 * p * #(1 - p) = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> true)))) /\
                     (0.5 * p = (prob ((x <-> true) /\ (z <-> true)))) /\
                     (0.5 * #(1 - p) = (prob ((y <-> false) /\ (z <-> true)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_true p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_true_y_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_true_z_true p q Hp0 Hp1 Hq0 Hq1)|apply (y_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> false))) /\
                     (0.5 * q * #(1 - q) = (prob ((x <-> true) /\ (y <-> false) /\ (z <-> false)))) /\
                     (0.5 * q = (prob ((x <-> true) /\ (z <-> false)))) /\
                     (0.5 * #(1 - q) = (prob ((y <-> false) /\ (z <-> false)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_false p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_true_y_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_true_z_false p q Hp0 Hp1 Hq0 Hq1)|apply (y_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> true))) /\
                     (0.5 * #(1 - p) * p = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> true)))) /\
                     (0.5 * #(1 - p) = (prob ((x <-> false) /\ (z <-> true)))) /\
                     (0.5 * p = (prob ((y <-> true) /\ (z <-> true)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_true p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_false_y_true_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)|apply (y_true_z_true p q Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> false))) /\
                     (0.5 * #(1 - q) * q = (prob ((x <-> false) /\ (y <-> true) /\ (z <-> false)))) /\
                     (0.5 * #(1 - q) = (prob ((x <-> false) /\ (z <-> false)))) /\
                     (0.5 * q = (prob ((y <-> true) /\ (z <-> false)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_false p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_false_y_true_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)|apply (y_true_z_false p q Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> true))) /\
                     (0.5 * #(1 - p) * #(1 - p) = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> true)))) /\
                     (0.5 * #(1 - p) = (prob ((x <-> false) /\ (z <-> true)))) /\
                     (0.5 * #(1 - p) = (prob ((y <-> false) /\ (z <-> true)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_true p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_false_y_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)|apply (y_false_z_true p q (1 - p) eq_refl Hp0 Hp1 Hq0 Hq1)]]].
  - apply HConseqRight with (post := {{ (0.5 = (prob (z <-> false))) /\
                     (0.5 * #(1 - q) * #(1 - q) = (prob ((x <-> false) /\ (y <-> false) /\ (z <-> false)))) /\
                     (0.5 * #(1 - q) = (prob ((x <-> false) /\ (z <-> false)))) /\
                     (0.5 * #(1 - q) = (prob ((y <-> false) /\ (z <-> false)))) }}).
    + indep_side.
    + apply HAnd; [apply (z_false p q Hp0 Hp1 Hq0 Hq1)|apply HAnd;
        [apply (x_false_y_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)|apply HAnd;
          [apply (x_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)|apply (y_false_z_false p q (1 - q) eq_refl Hp0 Hp1 Hq0 Hq1)]]].
Qed.

Lemma toss_stmt (Z : bool) :
  hoare_derivable {{ (prob true) = 1 }} <{ z toss 0.5 }> {{ (prob (z <-> Z)) = 0.5 }}.
Proof.
  apply HConseqLeft with (pre' := toss_pformula z 0.5 {{ (prob (z <-> Z)) = 0.5 }}).
  - destruct Z; cs_side.
  - apply HBoolToss. unfold coin_probability_valid; lra.
Qed.

Theorem cond_indep (X Y Z : bool) (p q : R)
  (Hp0 : 0 <= p) (Hp1 : p <= 1) (Hq0 : 0 <= q) (Hq1 : q <= 1) :
  hoare_derivable {{ (prob true) = 1 }} (CondSamples p q) (post_cond X Y Z).
Proof.
  unfold CondSamples. apply HSeq with (eta2 := {{ (prob (z <-> Z)) = 0.5 }}).
  - apply toss_stmt.
  - apply if_then_indep; assumption.
Qed.

End CondSamples.
