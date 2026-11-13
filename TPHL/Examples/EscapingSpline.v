(** The escaping spline.

    [x := 1; while 1 <= x do (Smp; if val = 0 then x := 0 else x := x + 1)],
    where the sampler [Smp] sets [val] to 0 with probability [1/(x+1)].
    Started at [x = 1], the loop reaches [x = 0] with probability at least
    [1 - 1/(n+1)] for every [n > 0] ([Espline_term]), by [W^LB] with the [n]
    regions [x = 1], ..., [x = n].

    The sampler is a section variable [Smp] with the hypothesis
    [HS : sampler_spec Smp] (see [SamplerSpec.v]); after the section every
    theorem is generic in [Smp] and [HS].  Nothing is assumed globally.
    Regions are [x = n - i] for [i < n], starting from region [n - 1]
    ([x = 1]); the regions, transitions, exits and solution are the
    nat-indexed functions [regions], [trans], [exits], [sol].  Logic
    variables are removed with [HInstantiate]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List Arith.PeanoNat.
Require Import PHL Examples.Lib Examples.PrAtoms Examples.SamplerSpec.
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

(** Rewrite every [Pr g] in the goal using a hypothesis [Pr h = Pr c]. *)
Ltac cconc :=
  repeat match goal with
  | Hps : pstate_admissible ?ps, H : Pr[?ps] ?h = Pr[?ps] ?c |- context [Pr[?ps] ?g] =>
      tryif constr_eq g h then fail else
      tryif constr_eq g c then fail else
      first [ rewrite (Pr_cconc_in ps h c g Hps H) by cdec
            | rewrite (Pr_cconc_out ps h c g Hps H) by cdec ]
  end.

(** Add the symmetric copy of every equation between formula probabilities. *)
Ltac sym_hyps :=
  repeat match goal with
  | H : Pr[?ps] ?a = Pr[?ps] ?b |- _ =>
      lazymatch goal with
      | _ : Pr[ps] b = Pr[ps] a |- _ => fail
      | _ => pose proof (eq_sym H)
      end
  end.

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

(** If all mass sits on [h], [Pr(g) = Pr(h /\ g)]. *)
Lemma Pr_conc_and (ps : Pstate) (h g : CFormula) :
  pstate_admissible ps -> Pr[ps] h = Pr[ps] c_true -> Pr[ps] g = Pr[ps] (c_and h g).
Proof.
  intros Hps Hh.
  rewrite (Pr_split ps Hps g h).
  rewrite (Pr_ext ps (c_and g h) (c_and h g))
    by (intros v; rewrite !satisfies_and; tauto).
  pose proof (Pr_split ps Hps c_true h) as Ht.
  rewrite (Pr_ext ps (c_and c_true h) h) in Ht
    by (intros v; rewrite satisfies_and; pose proof (satisfies_true v); tauto).
  pose proof (Pr_mono ps Hps (c_and g (c_not h)) (c_and c_true (c_not h))
                (fun v Hv => ltac:(rewrite satisfies_and in *; pose proof (satisfies_true v); tauto))).
  pose proof (Pr_nonneg ps (c_and g (c_not h))). lra.
Qed.

(** A finite conjunction of postconditions is derivable pointwise. *)
Lemma derive_finite_p_and pre (c : Cmd) m (f : nat -> PFormula) :
  (forall j, (j < m)%nat -> hoare_derivable pre c (f j)) ->
  hoare_derivable pre c (finite_p_and m f).
Proof.
  induction m as [|m IH]; intros H; cbn [finite_p_and].
  - apply derive_true.
  - apply HAnd; [apply IH; intros j Hj; apply H; lia | apply H; lia].
Qed.

Lemma frs_ext m (g h : nat -> R) :
  (forall j, (j < m)%nat -> g j = h j) -> finite_r_sum m g = finite_r_sum m h.
Proof.
  induction m as [|m IH]; intros H; cbn [finite_r_sum]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H m) by lia. reflexivity.
Qed.

Lemma frs_ind m a (c : R) :
  finite_r_sum m (fun j => if Nat.eqb j a then c else 0) = if Nat.ltb a m then c else 0.
Proof.
  induction m as [|m IH]; cbn [finite_r_sum].
  - destruct (Nat.ltb_spec a 0); [lia|reflexivity].
  - rewrite IH. destruct (Nat.ltb_spec a m), (Nat.ltb_spec a (S m)), (Nat.eqb_spec m a);
      try lia; lra.
Qed.

Module EscapingSpline.

Notation x := (dom_program_var "x").
Notation val := (dom_program_var "val").
Notation y1 := (prob_logic_var "y1").
Notation y2 := (prob_logic_var "y2").

Definition ifc : Cmd :=
  <{ if val = #(0%nat) then x := #(0%nat) else x := x + #(1%nat) end }>.

Definition guard : CFormula := \{ #(1%nat) <= x \}.

(** [1/(k+1)] *)
Definition p (k : nat) : R := 1 / (INR k + 1).

Lemma p_pos k : 0 < p k.
Proof.
  unfold p, Rdiv. pose proof (pos_INR k). rewrite Rmult_1_l. apply Rinv_0_lt_compat; lra.
Qed.

Lemma p_le1 k : p k <= 1.
Proof.
  unfold p. pose proof (pos_INR k).
  apply (Rmult_le_reg_r (INR k + 1)); [lra|]. field_simplify; lra.
Qed.

Ltac es_side := ptrans; pvalid; split_hyps; sym_hyps; cconc.

(** * The branches *)

Theorem ifthen_01 (k : nat) :
  hoare_derivable {{ #(p k) = (prob true) /\ y1 = #(p k) }}
    <{ x := #(0%nat) }> {{ y1 = (prob (x = #(0%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ #(0%nat) \} {{ y1 = (prob (x = #(0%nat))) }}).
  - ptrans; pvalid; split_hyps. pcanon [\{ true \}]. unfold Pc in *. lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_02 (k : nat) :
  hoare_derivable {{ #(1 - p k) = (prob true) /\ y2 = 0 }}
    <{ x := x + #(1%nat) }> {{ y2 = (prob (x = #(0%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ x + #(1%nat) \} {{ y2 = (prob (x = #(0%nat))) }}).
  - ptrans; pvalid; split_hyps. pcanon [\{ true \}]. unfold Pc in *. lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_0_int (k : nat) :
  hoare_derivable
    {{ ((#(p k) = (prob (val = #(0%nat))) /\ #(1 - p k) = (prob (~ (val = #(0%nat))))) /\
        y1 = #(p k)) /\ y2 = 0 }}
    ifc {{ y1 + y2 = (prob (x = #(0%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := if_precondition
                                    {{ #(p k) = (prob true) /\ y1 = #(p k) }}
                                    {{ #(1 - p k) = (prob true) /\ y2 = 0 }}
                                    \{ val = #(0%nat) \}).
  - ptrans; pvalid; split_hyps.
    pcanon [\{ val = #(0%nat) \}; \{ ~ (val = #(0%nat)) \}]. unfold Pc in *. repeat split; lra.
  - apply HIfEq; [apply ifthen_01 | apply ifthen_02].
Qed.

Theorem ifthen_0 (k : nat) :
  hoare_derivable
    {{ #(p k) = (prob (val = #(0%nat))) /\ #(1 - p k) = (prob (~ (val = #(0%nat)))) }}
    ifc {{ #(p k) = (prob (x = #(0%nat))) }}.
Proof.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst (p k))
               {{ (#(p k) = (prob (val = #(0%nat))) /\ #(1 - p k) = (prob (~ (val = #(0%nat))))) /\
                  y1 = #(p k) }})
    (eta2 := subst_prob_pformula y1 (PConst (p k)) {{ y1 + 0 = (prob (x = #(0%nat))) }}).
  - ptrans; pvalid; split_hyps. repeat split; lra.
  - apply HInstantiate.
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst 0)
                 {{ ((#(p k) = (prob (val = #(0%nat))) /\ #(1 - p k) = (prob (~ (val = #(0%nat))))) /\
                     y1 = #(p k)) /\ y2 = 0 }})
      (eta2 := subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = #(0%nat))) }}).
    + ptrans; pvalid; split_hyps. repeat split; lra.
    + apply HInstantiate. apply ifthen_0_int.
    + ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem ifthen_11 (k : nat) :
  hoare_derivable {{ #(p k) = (prob (x = k)) /\ y1 = 0 }}
    <{ x := #(0%nat) }> {{ y1 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ #(0%nat) \} {{ y1 = (prob (x = #((k + 1)%nat))) }}).
  - ptrans; pvalid; split_hyps. pcanon (@nil CFormula). lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_12 (k : nat) :
  hoare_derivable {{ #(1 - p k) = (prob (x = k)) /\ y2 = #(1 - p k) }}
    <{ x := x + #(1%nat) }> {{ y2 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ x + #(1%nat) \} {{ y2 = (prob (x = #((k + 1)%nat))) }}).
  - ptrans; pvalid; split_hyps. pcanon [\{ x = k \}]. unfold Pc in *. lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_1_int (k : nat) :
  hoare_derivable
    {{ ((#(p k) = (prob (x = k /\ val = #(0%nat))) /\
         #(1 - p k) = (prob (x = k /\ ~ (val = #(0%nat))))) /\ y1 = 0) /\ y2 = #(1 - p k) }}
    ifc {{ y1 + y2 = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseqLeft with (pre' := if_precondition
                                    {{ #(p k) = (prob (x = k)) /\ y1 = 0 }}
                                    {{ #(1 - p k) = (prob (x = k)) /\ y2 = #(1 - p k) }}
                                    \{ val = #(0%nat) \}).
  - ptrans; pvalid; split_hyps.
    pcanon [\{ x = k /\ val = #(0%nat) \}; \{ x = k /\ ~ (val = #(0%nat)) \}].
    unfold Pc in *. repeat split; lra.
  - apply HIfEq; [apply ifthen_11 | apply ifthen_12].
Qed.

Theorem ifthen_1 (k : nat) :
  hoare_derivable
    {{ #(p k) = (prob (x = k /\ val = #(0%nat))) /\
       #(1 - p k) = (prob (x = k /\ ~ (val = #(0%nat)))) }}
    ifc {{ #(1 - p k) = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 0)
               {{ (#(p k) = (prob (x = k /\ val = #(0%nat))) /\
                   #(1 - p k) = (prob (x = k /\ ~ (val = #(0%nat))))) /\ y1 = 0 }})
    (eta2 := subst_prob_pformula y1 (PConst 0)
               {{ y1 + #(1 - p k) = (prob (x = #((k + 1)%nat))) }}).
  - ptrans; pvalid; split_hyps. repeat split; lra.
  - apply HInstantiate.
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst (1 - p k))
                 {{ ((#(p k) = (prob (x = k /\ val = #(0%nat))) /\
                      #(1 - p k) = (prob (x = k /\ ~ (val = #(0%nat))))) /\ y1 = 0) /\
                    y2 = #(1 - p k) }})
      (eta2 := subst_prob_pformula y2 (PConst (1 - p k))
                 {{ y1 + y2 = (prob (x = #((k + 1)%nat))) }}).
    + ptrans; pvalid; split_hyps. repeat split; lra.
    + apply HInstantiate. apply ifthen_1_int.
    + ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

Theorem ifthen_void1 (k k1 : nat) : k1 <> 0%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable {{ (prob (x = k)) = (prob true) /\ y1 = 0 }}
    <{ x := #(0%nat) }> {{ y1 = (prob (x = k1)) }}.
Proof.
  intros H1 H2.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ #(0%nat) \} {{ y1 = (prob (x = k1)) }}).
  - ptrans; pvalid; split_hyps. pcanon (@nil CFormula). lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_void2 (k k1 : nat) : k1 <> 0%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable {{ (prob (x = k)) = (prob true) /\ y2 = 0 }}
    <{ x := x + #(1%nat) }> {{ y2 = (prob (x = k1)) }}.
Proof.
  intros H1 H2.
  apply HConseqLeft with (pre' := subst_dom_pformula x \{ x + #(1%nat) \} {{ y2 = (prob (x = k1)) }}).
  - es_side. lra.
  - apply HDomAssign.
Qed.

Theorem ifthen_void_int (k k1 : nat) : k1 <> 0%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (((prob (val = #(0%nat))) = (prob (x = k /\ val = #(0%nat))) /\
         (prob (~ (val = #(0%nat)))) = (prob (x = k /\ ~ (val = #(0%nat))))) /\ y1 = 0) /\
       y2 = 0 }}
    ifc {{ y1 + y2 = (prob (x = k1)) }}.
Proof.
  intros H1 H2.
  apply HConseqLeft with (pre' := if_precondition
                                    {{ (prob (x = k)) = (prob true) /\ y1 = 0 }}
                                    {{ (prob (x = k)) = (prob true) /\ y2 = 0 }}
                                    \{ val = #(0%nat) \}).
  - es_side. repeat split; lra.
  - apply HIfEq; [apply ifthen_void1 | apply ifthen_void2]; assumption.
Qed.

Theorem ifthen_void (k k1 : nat) : k1 <> 0%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable
    {{ (prob (val = #(0%nat))) = (prob (x = k /\ val = #(0%nat))) /\
       (prob (~ (val = #(0%nat)))) = (prob (x = k /\ ~ (val = #(0%nat)))) }}
    ifc {{ 0 = (prob (x = k1)) }}.
Proof.
  intros H1 H2.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 0)
               {{ ((prob (val = #(0%nat))) = (prob (x = k /\ val = #(0%nat))) /\
                   (prob (~ (val = #(0%nat)))) = (prob (x = k /\ ~ (val = #(0%nat))))) /\ y1 = 0 }})
    (eta2 := subst_prob_pformula y1 (PConst 0) {{ 0 + y1 = (prob (x = k1)) }}).
  - ptrans; pvalid; split_hyps. repeat split; lra.
  - apply HInstantiate.
    apply HConseq with
      (eta1 := subst_prob_pformula y2 (PConst 0)
                 {{ (((prob (val = #(0%nat))) = (prob (x = k /\ val = #(0%nat))) /\
                      (prob (~ (val = #(0%nat)))) = (prob (x = k /\ ~ (val = #(0%nat))))) /\
                     y1 = 0) /\ y2 = 0 }})
      (eta2 := subst_prob_pformula y2 (PConst 0) {{ y1 + y2 = (prob (x = k1)) }}).
    + ptrans; pvalid; split_hyps. repeat split; lra.
    + apply HInstantiate. apply ifthen_void_int; assumption.
    + ptrans; pvalid. lra.
  - ptrans; pvalid. lra.
Qed.

(** * The loop, for any sampler meeting the specification *)

Section Spline.
Variable Smp : Cmd.
Hypothesis HS : SamplerSpec.sampler_spec Smp.

Definition body : Cmd := CSeq Smp ifc.
Definition Espline_loop : Cmd := CWhile guard body.
Definition Escaping_spline : Cmd := CSeq (CDomAssign x (tnat 1)) Espline_loop.

(** All mass on [x = k] (the sampler's precondition). *)
Definition bpre (k : nat) : PFormula :=
  {{ (prob (x = k)) = 1 /\ (prob (x = k)) = (prob true) }}.

Theorem bodyvoid (k k1 : nat) : k1 <> 0%nat -> k1 <> (k + 1)%nat ->
  hoare_derivable {{ (prob (x = k)) = 1 /\ (prob (x = k)) = (prob true) }}
    body {{ 0 = (prob (x = k1)) }}.
Proof.
  intros H1 H2. apply HSeq with (eta2 := {{ (prob (x = k)) = (prob true) }}).
  - exact (SamplerSpec.spec_xinv Smp HS k).
  - apply HConseqLeft with
      (pre' := {{ (prob (val = #(0%nat))) = (prob (x = k /\ val = #(0%nat))) /\
                  (prob (~ (val = #(0%nat)))) = (prob (x = k /\ ~ (val = #(0%nat)))) }}).
    + pvalid; split_hyps.
      rewrite <- !(Pr_conc_and ps \{ x = k \}) by assumption. split; reflexivity.
    + apply (ifthen_void k k1 H1 H2).
Qed.

(** The body uses the three fields of [sampler_spec]. *)
Theorem body0 (k : nat) :
  hoare_derivable {{ (prob (x = k)) = 1 /\ (prob (x = k)) = (prob true) }}
    body {{ #(p k) = (prob (x = #(0%nat))) }}.
Proof.
  apply HSeq with
    (eta2 := {{ (prob (x = k /\ val = #(0%nat))) = #(p k) /\
                (prob (x = k /\ ~ (val = #(0%nat)))) = #(1 - p k) /\
                (prob (x = k)) = (prob true) }}).
  - apply HAnd; [exact (SamplerSpec.spec_zero Smp HS k)|].
    apply HAnd; [exact (SamplerSpec.spec_nonzero Smp HS k)|].
    apply HConseqRight with (post := {{ (prob (x = k)) = (prob true) }}).
    + pvalid. lra.
    + exact (SamplerSpec.spec_xinv Smp HS k).
  - apply HConseqLeft with
      (pre' := {{ #(p k) = (prob (val = #(0%nat))) /\ #(1 - p k) = (prob (~ (val = #(0%nat)))) }}).
    + pvalid; split_hyps.
      rewrite (Pr_conc_and ps \{ x = k \} \{ val = #(0%nat) \}) by assumption.
      rewrite (Pr_conc_and ps \{ x = k \} \{ ~ (val = #(0%nat)) \}) by assumption.
      split; lra.
    + apply ifthen_0.
Qed.

Theorem body1 (k : nat) :
  hoare_derivable {{ (prob (x = k)) = 1 /\ (prob (x = k)) = (prob true) }}
    body {{ #(1 - p k) = (prob (x = #((k + 1)%nat))) }}.
Proof.
  apply HSeq with
    (eta2 := {{ #(p k) = (prob (x = k /\ val = #(0%nat))) /\
                #(1 - p k) = (prob (x = k /\ ~ (val = #(0%nat)))) }}).
  - apply HConseqRight with
      (post := {{ (prob (x = k /\ val = #(0%nat))) = #(p k) /\
                  (prob (x = k /\ ~ (val = #(0%nat)))) = #(1 - p k) }}).
    + pvalid; split_hyps. split; lra.
    + apply HAnd; [exact (SamplerSpec.spec_zero Smp HS k)
                  | exact (SamplerSpec.spec_nonzero Smp HS k)].
  - apply ifthen_1.
Qed.

(** ** The while rule *)

(** Region [i] is [x = n - i]. *)
Definition regions (n i : nat) : CFormula := \{ x = #((n - i)%nat) \}.

(** From [x = n - i] the body moves to [x = n - i + 1] (region [i - 1]) with
    [1 - 1/(n-i+1)] and exits into [x = 0] with [1/(n-i+1)]. *)
Definition trans (n i j : nat) : R := if Nat.eqb (S j) i then 1 - p (n - i) else 0.
Definition exits (n i : nat) : R := p (n - i).

(** The solution [1 - (n-i)/(n+1)]. *)
Definition sol (n i : nat) : R := 1 - INR (n - i) / (INR n + 1).

Lemma helper1 n : while_regions_in_guard n guard (regions n).
Proof. unfold while_regions_in_guard, cformula_valid, guard, regions. intros i Hi. cdecide. Qed.

Lemma helper2 n : while_regions_disjoint n (regions n).
Proof. unfold while_regions_disjoint, cformula_valid, regions. intros i j Hi Hj. cdecide. Qed.

Lemma helper3 n : while_progress n (trans n) (exits n).
Proof. intros i Hi. left. apply p_pos. Qed.

(** The body premise of [W^LB] for region [i]: [body1]
    for the next region, [bodyvoid] for the others, [body0] for the exit. *)
Lemma helper4 n i : (i < n)%nat ->
  hoare_derivable (p_concentrated_unit (regions n i)) body
    (while_body_post_lower n (regions n) (trans n i) guard \{ x = #(0%nat) \} (exits n i)).
Proof.
  intros Hi.
  assert (Hpre : pformula_valid (PFImpl (p_concentrated_unit (regions n i)) (bpre (n - i)))).
  { unfold regions, bpre. pvalid. split_hyps. split; lra. }
  unfold while_body_post_lower. apply HAnd.
  - apply derive_finite_p_and. intros j Hj. unfold trans.
    destruct (Nat.eqb_spec (S j) i) as [<-|Hne].
    + apply HConseq with (eta1 := bpre (n - S j))
        (eta2 := {{ #(1 - p (n - S j)) = (prob (x = #((n - S j + 1)%nat))) }}).
      * exact Hpre.
      * apply (body1 (n - S j)).
      * unfold regions. replace (n - S j + 1)%nat with (n - j)%nat by lia.
        ptrans; pvalid. lra.
    + apply HConseq with (eta1 := bpre (n - i)) (eta2 := {{ 0 = (prob (x = #((n - j)%nat))) }}).
      * exact Hpre.
      * apply (bodyvoid (n - i) (n - j)); lia.
      * unfold regions. ptrans; pvalid. lra.
  - apply HConseq with (eta1 := bpre (n - i)) (eta2 := {{ #(p (n - i)) = (prob (x = #(0%nat))) }}).
    + exact Hpre.
    + apply (body0 (n - i)).
    + unfold exits, guard. ptrans; pvalid. pcanon [\{ x = #(0%nat) \}]. unfold Pc in *. lra.
Qed.

Lemma frs_zero m : finite_r_sum m (fun _ => 0) = 0.
Proof. induction m as [|m IH]; cbn [finite_r_sum]; lra. Qed.

Lemma sol_ok n : (n > 0)%nat -> while_lower_solution n (sol n) (trans n) (exits n).
Proof.
  intros Hn i Hi. pose proof (pos_INR n).
  assert (Hle : INR (n - i) <= INR n) by (apply le_INR; lia).
  pose proof (pos_INR (n - i)).
  split.
  - destruct i as [|i]; unfold trans, exits.
    + rewrite (frs_ext n _ (fun _ => 0)) by (intros j _; cbn [Nat.eqb]; lra).
      rewrite frs_zero. unfold sol, p. rewrite Nat.sub_0_r. right. field. lra.
    + rewrite (frs_ext n _ (fun j => if Nat.eqb j i then (1 - p (n - S i)) * sol n i else 0)).
      * rewrite frs_ind. destruct (Nat.ltb_spec i n); [|lia].
        unfold sol, p. replace (n - i)%nat with (S (n - S i)) by lia. rewrite S_INR.
        pose proof (pos_INR (n - S i)). right. field. lra.
      * intros j _. cbn [Nat.eqb]. destruct (Nat.eqb_spec j i); [subst; reflexivity | lra].
  - unfold sol.
    assert (Hq : INR (n - i) / (INR n + 1) <= 1).
    { apply (Rmult_le_reg_r (INR n + 1)); [lra|]. unfold Rdiv.
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (0 <= INR (n - i) / (INR n + 1)).
    { unfold Rdiv. apply Rmult_le_pos; [lra|]. left; apply Rinv_0_lt_compat; lra. }
    split; lra.
Qed.

(** The solution at [x = 1], region [n - 1]. *)
Lemma helper6 n : (n > 0)%nat -> sol n (n - 1) = 1 - 1 / (INR n + 1).
Proof. intros Hn. unfold sol. replace (n - (n - 1))%nat with 1%nat by lia. cbn [INR]. reflexivity. Qed.

(** ** Termination *)

Theorem Espline_term_int (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (#(1%nat) <= x /\ x = #(1%nat))) >= y1 /\
       (prob (#(1%nat) <= x /\ x = #(1%nat))) = (prob true) }}
    Espline_loop
    {{ #(1 - 1 / (INR n + 1)) * y1 <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn.
  (* [HWhileLower] states its pre- and postcondition as
     [box (beta /\ G_k) /\ y <= Pr(true)] and [x_k * y <= Pr(gamma)],
     hence the two consequences. *)
  eapply HConseqRight; [|eapply HConseqLeft;
    [|apply (HWhileLower n (n - 1) guard \{ x = #(0%nat) \} body (regions n) (sol n)
             (exits n) (trans n) y1)]].
  - rewrite <- (helper6 n Hn). ptrans; pvalid. lra.
  - unfold guard, regions. replace (n - (n - 1))%nat with 1%nat by lia.
    ptrans; pvalid; split_hyps.
    pcanon [\{ #(1%nat) <= x /\ x = #(1%nat) \}; \{ true \}]. unfold Pc in *. split; lra.
  - lia.
  - apply helper1.
  - apply helper2.
  - apply helper3.
  - exact (helper4 n).
  - exact (sol_ok n Hn).
Qed.

Theorem Espline_term_y (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true) }}
    Espline_loop
    {{ #(1 - 1 / (INR n + 1)) * y1 <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn.
  apply HConseqLeft with
    (pre' := {{ (prob (#(1%nat) <= x /\ x = #(1%nat))) >= y1 /\
                (prob (#(1%nat) <= x /\ x = #(1%nat))) = (prob true) }}).
  - ptrans; pvalid; split_hyps. pcanon [\{ x = #(1%nat) \}; \{ true \}]. unfold Pc in *.
    split; lra.
  - apply (Espline_term_int n Hn).
Qed.

Theorem Espline_term_elim_y (n : nat) : (n > 0)%nat ->
  hoare_derivable
    {{ (prob (x = #(1%nat))) >= 1 /\ (prob (x = #(1%nat))) = (prob true) }}
    Espline_loop
    {{ #(1 - 1 / (INR n + 1)) <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn.
  apply HConseq with
    (eta1 := subst_prob_pformula y1 (PConst 1)
               {{ ((prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true)) /\ y1 = 1 }})
    (eta2 := subst_prob_pformula y1 (PConst 1)
               {{ #(1 - 1 / (INR n + 1)) * y1 <= (prob (x = #(0%nat))) }}).
  - ptrans; pvalid; split_hyps. repeat split; lra.
  - apply HInstantiate.
    apply HConseqLeft with
      (pre' := {{ (prob (x = #(1%nat))) >= y1 /\ (prob (x = #(1%nat))) = (prob true) }}).
    + ptrans; pvalid; split_hyps. split; lra.
    + apply (Espline_term_y n Hn).
  - ptrans; pvalid. lra.
Qed.

(** Started anywhere with total mass 1, the escaping spline reaches [x = 0]
    with probability at least [1 - 1/(n+1)], for every [n > 0]. *)
Theorem Espline_term (n : nat) : (n > 0)%nat ->
  hoare_derivable {{ (prob true) = 1 }} Escaping_spline
    {{ #(1 - 1 / (INR n + 1)) <= (prob (x = #(0%nat))) }}.
Proof.
  intros Hn. unfold Escaping_spline.
  apply HSeq with (eta2 := {{ (prob (x = #(1%nat))) = 1 /\ (prob (x = #(1%nat))) = (prob true) }}).
  - apply HConseqLeft with
      (pre' := subst_dom_pformula x (tnat 1)
                 {{ (prob (x = #(1%nat))) = 1 /\ (prob (x = #(1%nat))) = (prob true) }}).
    + ptrans; pvalid. pcanon [\{ true \}]. unfold Pc in *. split; lra.
    + apply HDomAssign.
  - apply HConseqLeft with
      (pre' := {{ (prob (x = #(1%nat))) >= 1 /\ (prob (x = #(1%nat))) = (prob true) }}).
    + ptrans; pvalid; split_hyps. split; lra.
    + apply (Espline_term_elim_y n Hn).
Qed.

End Spline.

End EscapingSpline.
