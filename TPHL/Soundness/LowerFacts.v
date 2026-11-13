(** Real-number facts used by [W^LB]: finite additivity over a disjoint
    family of formulas, and bounds on weighted indicator sums. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require boolp.
Require Import MeasureIntegration PHL.
Require Import Soundness.SplitRules Soundness.LowerCertificate.

Local Open Scope R_scope.

Section DisjointFamily.
Context {D : Domain}.

(** [sum_j mu(A_j) + mu(B) <= mu(tt)] for pairwise disjoint [A_j] and [B]. *)
Lemma fsum_disjoint_le (mu : Measure D) m (A : nat -> Assertion D) (B : Assertion D) :
  Subprob mu ->
  (forall i j, (i < m)%nat -> (j < i)%nat -> forall v, ~ (A i v /\ A j v)) ->
  (forall j, (j < m)%nat -> forall v, ~ (A j v /\ B v)) ->
  finite_r_sum m (fun j => measure_of mu (A j)) + measure_of mu B <=
  measure_of mu (fun _ => True).
Proof.
  intros h hA hB.
  pose proof (ConcreteMeasure.subprob_finite h) as hfin.
  set (U := fun m' v => (exists j, (j < m')%nat /\ A j v) \/ B v).
  assert (hU : forall m', (m' <= m)%nat ->
            finite_r_sum m' (fun j => measure_of mu (A j)) + measure_of mu B =
            measure_of mu (U m')).
  { induction m' as [|m' IH]; intros hm'; cbn [finite_r_sum].
    - rewrite (measure_extensional mu (U 0%nat) B); [lra|].
      intros v. unfold U. split; [intros [[j [hj _]]|hv]; [lia|exact hv] | intros hv; right; exact hv].
    - rewrite (measure_extensional mu (U (S m'))
                 (fun v => U m' v \/ A m' v)).
      + rewrite measure_additive; [| exact hfin |].
        * rewrite <- IH by lia. lra.
        * intros v [[[j [hj hjv]] | hBv] hAv].
          -- exact (hA m' j ltac:(lia) hj v (conj hAv hjv)).
          -- exact (hB m' ltac:(lia) v (conj hAv hBv)).
      + intros v. unfold U. split.
        * intros [[j [hj hjv]] | hBv]; [|left; right; exact hBv].
          destruct (Nat.eq_dec j m') as [->|hne]; [right; exact hjv|].
          left; left; exists j; split; [lia | exact hjv].
        * intros [[[j [hj hjv]] | hBv] | hAv].
          -- left; exists j; split; [lia | exact hjv].
          -- right; exact hBv.
          -- left; exists m'; split; [lia | exact hAv]. }
  rewrite (hU m (le_n m)).
  apply measure_of_monotone; [exact h | intros; exact I].
Qed.

End DisjointFamily.

(** With pairwise disjoint events, a weighted indicator sum is at most the
    largest weight of an event that occurs. *)
Lemma fsum_disjoint_indicator_le m (P : nat -> Prop) (c : nat -> R) (bound : R) :
  (forall i j, (i < m)%nat -> (j < i)%nat -> ~ (P i /\ P j)) ->
  (forall j, (j < m)%nat -> P j -> c j <= bound) -> 0 <= bound ->
  finite_r_sum m (fun j => c j * (if boolp.pselect (P j) then R1 else R0)) <= bound.
Proof.
  intros hdis hc hb.
  assert (hzero : forall m', (forall j, (j < m')%nat -> ~ P j) ->
            finite_r_sum m' (fun j => c j * (if boolp.pselect (P j) then R1 else R0)) = 0).
  { induction m' as [|m' IH]; intros hn; cbn [finite_r_sum]; [reflexivity|].
    rewrite IH by (intros j hj; apply hn; lia).
    destruct (boolp.pselect (P m')) as [hP|_]; [exfalso; exact (hn m' ltac:(lia) hP) | lra]. }
  assert (H : forall m', (m' <= m)%nat ->
            finite_r_sum m' (fun j => c j * (if boolp.pselect (P j) then R1 else R0)) <= bound).
  { induction m' as [|m' IH]; intros hm'; cbn [finite_r_sum]; [exact hb|].
    destruct (boolp.pselect (P m')) as [hP|hnP].
    - rewrite hzero; [pose proof (hc m' ltac:(lia) hP); lra|].
      intros j hj hPj. exact (hdis m' j ltac:(lia) hj (conj hP hPj)).
    - pose proof (IH ltac:(lia)). lra. }
  exact (H m (le_n m)).
Qed.

(** Replacing the certificate by its nonnegative part keeps the
    post-fixed-point inequality, since [x >= 0]. *)
Lemma post_fixed_nonneg_part m (x : nat -> R) (r : nat -> R) (e : R) (xi : R) :
  (forall j, (j < m)%nat -> 0 <= x j) ->
  xi <= finite_r_sum m (fun j => r j * x j) + e ->
  xi <= finite_r_sum m (fun j => Rmax (r j) 0 * x j) + Rmax e 0.
Proof.
  intros hx h.
  assert (finite_r_sum m (fun j => r j * x j) <= finite_r_sum m (fun j => Rmax (r j) 0 * x j)).
  { apply finite_r_sum_le. intros j hj. apply Rmult_le_compat_r; [exact (hx j hj) | apply Rmax_l]. }
  pose proof (Rmax_l e 0). lra.
Qed.
