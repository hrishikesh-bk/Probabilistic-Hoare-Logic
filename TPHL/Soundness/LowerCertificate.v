(** The linear-algebra core of [W^LB] (App. C, Lemma 17), stated over plain
    reals.  For a sub-stochastic system [Q(z)_i = sum_j q_ij z_j + e_i] with
    the progress condition, every post-fixed point [x <= Q(x)] lies below every
    pre-fixed point [l >= Q(l)].

    The argument is a maximum-difference argument instead of the paper's
    matrix powers: if [d = x - l] had a positive maximum [M], the least index
    attaining it would have to move all its mass to indices also attaining
    [M], and progress says one of them is smaller.

    Rows are only constrained on a set [N] of "live" indices.  In the
    application [N] holds of the nonempty regions: a body triple whose
    precondition is unsatisfiable carries no information, so the paper's row
    bound [sum_j q_ij + q_i <= 1] is only available on nonempty regions. *)
From Stdlib Require Import Reals Lra Lia Wf_nat.
From mathcomp Require boolp.
Require Import PHL.

Local Open Scope R_scope.

Section FiniteSums.

Lemma finite_r_sum_ext m f g :
  (forall j, (j < m)%nat -> f j = g j) -> finite_r_sum m f = finite_r_sum m g.
Proof.
  induction m as [|m IH]; intros H; cbn; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma finite_r_sum_le m f g :
  (forall j, (j < m)%nat -> f j <= g j) -> finite_r_sum m f <= finite_r_sum m g.
Proof.
  induction m as [|m IH]; intros H; cbn; [lra|].
  pose proof (IH (fun j Hj => H j ltac:(lia))). pose proof (H m ltac:(lia)). lra.
Qed.

Lemma finite_r_sum_nonneg m f :
  (forall j, (j < m)%nat -> 0 <= f j) -> 0 <= finite_r_sum m f.
Proof.
  intros H. induction m as [|m' IH]; cbn; [lra|].
  pose proof (IH (fun j Hj => H j ltac:(lia))). pose proof (H m' ltac:(lia)). lra.
Qed.

Lemma finite_r_sum_zero m : finite_r_sum m (fun _ => 0) = 0.
Proof. induction m; cbn; lra. Qed.

Lemma finite_r_sum_plus m f g :
  finite_r_sum m (fun j => f j + g j) = finite_r_sum m f + finite_r_sum m g.
Proof. induction m; cbn; lra. Qed.

Lemma finite_r_sum_minus m f g :
  finite_r_sum m (fun j => f j - g j) = finite_r_sum m f - finite_r_sum m g.
Proof. induction m; cbn; lra. Qed.

Lemma finite_r_sum_scale m c f :
  finite_r_sum m (fun j => c * f j) = c * finite_r_sum m f.
Proof. induction m; cbn; lra. Qed.

Lemma finite_r_sum_term m f j0 :
  (forall j, (j < m)%nat -> 0 <= f j) -> (j0 < m)%nat -> f j0 <= finite_r_sum m f.
Proof.
  induction m as [|m IH]; intros H Hj0; [lia|]. cbn.
  destruct (Nat.eq_dec j0 m) as [->|Hne].
  - pose proof (finite_r_sum_nonneg m f (fun j Hj => H j ltac:(lia))). lra.
  - pose proof (IH (fun j Hj => H j ltac:(lia)) ltac:(lia)). pose proof (H m ltac:(lia)). lra.
Qed.

(** A sum of nonnegative terms that is at most zero has only zero terms. *)
Lemma finite_r_sum_nonneg_zero m f :
  (forall j, (j < m)%nat -> 0 <= f j) -> finite_r_sum m f <= 0 ->
  forall j, (j < m)%nat -> f j = 0.
Proof.
  intros H Hs j Hj. pose proof (finite_r_sum_term m f j H Hj). pose proof (H j Hj). lra.
Qed.

End FiniteSums.

Section Maximum.
Variables (N : nat -> Prop) (d : nat -> R).

(** [max(0, max {d i | i < k, N i})]. *)
Fixpoint maxd (k : nat) : R :=
  match k with
  | O => 0
  | S k' => Rmax (maxd k') (if boolp.pselect (N k') then d k' else 0)
  end.

Lemma maxd_nonneg k : 0 <= maxd k.
Proof. induction k; cbn; [lra|]. eapply Rle_trans; [exact IHk | apply Rmax_l]. Qed.

Lemma maxd_upper k i : (i < k)%nat -> N i -> d i <= maxd k.
Proof.
  induction k as [|k IH]; intros Hi HN; [lia|]. cbn.
  destruct (Nat.eq_dec i k) as [->|Hne].
  - eapply Rle_trans; [|apply Rmax_r]. destruct (boolp.pselect (N k)); [lra | contradiction].
  - eapply Rle_trans; [apply IH; [lia | exact HN] | apply Rmax_l].
Qed.

Lemma maxd_attained k : 0 < maxd k -> exists i, (i < k)%nat /\ N i /\ d i = maxd k.
Proof.
  induction k as [|k IH]; cbn; intros Hpos; [lra|].
  unfold Rmax in *.
  destruct (Rle_dec (maxd k) (if boolp.pselect (N k) then d k else 0)) as [Hle|Hgt].
  - destruct (boolp.pselect (N k)) as [HN|HN]; [|lra].
    exists k. split; [lia|]. split; [exact HN | reflexivity].
  - destruct (IH Hpos) as [i [Hi [HN Hd]]]. exists i. split; [lia|]. split; [exact HN | exact Hd].
Qed.

End Maximum.

(** Classical least-element principle on [nat]. *)
Lemma exists_least (P : nat -> Prop) :
  (exists i, P i) -> exists i, P i /\ forall j, (j < i)%nat -> ~ P j.
Proof.
  intros [i Hi]. induction i as [i IH] using (well_founded_induction Wf_nat.lt_wf).
  destruct (Classical_Prop.classic (exists j, (j < i)%nat /\ P j)) as [[j [Hj HPj]]|Hno].
  - exact (IH j Hj HPj).
  - exists i. split; [exact Hi|]. intros j Hj HPj. apply Hno. exists j. split; assumption.
Qed.

Section LowerCertificate.
Variables (m : nat) (N : nat -> Prop).
Variables (q : nat -> nat -> R) (e : nat -> R) (x l : nat -> R).

Hypothesis q_nonneg : forall i j, 0 <= q i j.
Hypothesis e_nonneg : forall i, 0 <= e i.
Hypothesis row_sum : forall i, (i < m)%nat -> N i -> finite_r_sum m (q i) + e i <= 1.
Hypothesis dead_columns :
  forall i j, (i < m)%nat -> N i -> (j < m)%nat -> ~ N j -> q i j = 0.
Hypothesis progress :
  forall i, (i < m)%nat -> N i -> 0 < e i \/ exists j, (j < i)%nat /\ 0 < q i j.
Hypothesis x_post : forall i, (i < m)%nat -> N i ->
  x i <= finite_r_sum m (fun j => q i j * x j) + e i.
Hypothesis l_pre : forall i, (i < m)%nat -> N i ->
  finite_r_sum m (fun j => q i j * l j) + e i <= l i.

Theorem post_fixed_below_pre_fixed : forall i, (i < m)%nat -> N i -> x i <= l i.
Proof.
  set (dd := fun j => x j - l j).
  set (M := maxd N dd m).
  assert (HM0 : 0 <= M) by apply maxd_nonneg.
  assert (Hup : forall j, (j < m)%nat -> N j -> dd j <= M) by (intros; apply maxd_upper; assumption).
  (* Each live row: d_i <= sum_j q_ij d_j. *)
  assert (Hrow : forall i, (i < m)%nat -> N i -> dd i <= finite_r_sum m (fun j => q i j * dd j)).
  { intros i Hi HN. unfold dd.
    rewrite (finite_r_sum_ext m (fun j => q i j * (x j - l j))
               (fun j => q i j * x j - q i j * l j)) by (intros; ring).
    rewrite finite_r_sum_minus.
    pose proof (x_post i Hi HN). pose proof (l_pre i Hi HN). lra. }
  (* And sum_j q_ij d_j <= sum_j q_ij M. *)
  assert (Hbound : forall i, (i < m)%nat -> N i ->
            finite_r_sum m (fun j => q i j * dd j) <= finite_r_sum m (fun j => q i j * M)).
  { intros i Hi HN. apply finite_r_sum_le. intros j Hj.
    destruct (Classical_Prop.classic (N j)) as [HNj|HNj].
    - apply Rmult_le_compat_l; [apply q_nonneg | apply Hup; assumption].
    - rewrite (dead_columns i j Hi HN Hj HNj). lra. }
  destruct (Rle_lt_dec M 0) as [HMle|HMpos].
  { intros i Hi HN. pose proof (Hup i Hi HN). unfold dd in *. lra. }
  exfalso.
  destruct (exists_least (fun i => (i < m)%nat /\ N i /\ dd i = M))
    as [i0 [[Hi0 [HN0 Hd0]] Hleast]].
  { destruct (maxd_attained N dd m HMpos) as [i [Hi [HN Hd]]]. exists i. split; [exact Hi|]. split; [exact HN | exact Hd]. }
  pose proof (Hrow i0 Hi0 HN0) as R0. pose proof (Hbound i0 Hi0 HN0) as B0.
  pose proof (row_sum i0 Hi0 HN0) as S0.
  rewrite (finite_r_sum_ext m (fun j => q i0 j * M) (fun j => M * q i0 j)) in B0 by (intros; ring).
  rewrite finite_r_sum_scale in B0.
  (* M <= M * sum_j q_i0j <= M (1 - e_i0), so e_i0 = 0. *)
  assert (He0 : e i0 = 0).
  { pose proof (e_nonneg i0).
    assert (M * finite_r_sum m (q i0) <= M * (1 - e i0)) by (apply Rmult_le_compat_l; lra).
    assert (M * e i0 <= 0) by nra.
    destruct (Rle_lt_dec (e i0) 0); [lra|]. nra. }
  (* The slack terms q_i0j (M - d_j) vanish. *)
  assert (Hslack : forall j, (j < m)%nat -> q i0 j * (M - dd j) = 0).
  { apply finite_r_sum_nonneg_zero.
    - intros j Hj. destruct (Classical_Prop.classic (N j)) as [HNj|HNj].
      + apply Rmult_le_pos; [apply q_nonneg | pose proof (Hup j Hj HNj); lra].
      + rewrite (dead_columns i0 j Hi0 HN0 Hj HNj). lra.
    - rewrite (finite_r_sum_ext m (fun j => q i0 j * (M - dd j))
                 (fun j => M * q i0 j - q i0 j * dd j)) by (intros; ring).
      rewrite finite_r_sum_minus, finite_r_sum_scale.
      assert (M * finite_r_sum m (q i0) <= M * 1) by (apply Rmult_le_compat_l; lra).
      lra. }
  destruct (progress i0 Hi0 HN0) as [He|[j [Hj Hq]]]; [lra|].
  assert (Hjm : (j < m)%nat) by lia.
  assert (HNj : N j).
  { destruct (Classical_Prop.classic (N j)) as [HNj|HNj]; [exact HNj|].
    rewrite (dead_columns i0 j Hi0 HN0 Hjm HNj) in Hq. lra. }
  pose proof (Hslack j Hjm) as Hs.
  assert (dd j = M).
  { apply Rmult_integral in Hs. destruct Hs as [Hs|Hs]; lra. }
  exact (Hleast j Hj (conj Hjm (conj HNj H))).
Qed.

End LowerCertificate.
