(** Sorting by a natural-number key.  The progress condition of [W^LB] is
    stated on indices ([j < i]); ordering classes by the number of loop
    iterations needed to exit with positive probability satisfies it. *)
From Stdlib Require Import List Arith Lia Permutation Sorting.Sorted.
Import ListNotations.

Section SortByKey.
Context {X : Type} (key : X -> nat).

Fixpoint insertk (x : X) (l : list X) : list X :=
  match l with
  | [] => [x]
  | y :: l' => if Nat.leb (key x) (key y) then x :: l else y :: insertk x l'
  end.

Fixpoint sortk (l : list X) : list X :=
  match l with
  | [] => []
  | x :: l' => insertk x (sortk l')
  end.

Lemma insertk_perm x l : Permutation (insertk x l) (x :: l).
Proof.
  induction l as [|y l IH]; cbn; [reflexivity|].
  destruct (Nat.leb (key x) (key y)); [reflexivity|].
  rewrite IH. apply perm_swap.
Qed.

Lemma sortk_perm l : Permutation (sortk l) l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite insertk_perm, IH. reflexivity.
Qed.

Local Notation Rk := (fun a b => key a <= key b).

Lemma insertk_sorted x l : StronglySorted Rk l -> StronglySorted Rk (insertk x l).
Proof.
  induction l as [|y l IH]; intros H; cbn.
  - constructor; constructor.
  - inversion H as [|? ? Hl Hf]; subst.
    destruct (Nat.leb (key x) (key y)) eqn:E.
    + apply Nat.leb_le in E. constructor; [exact H|].
      constructor; [exact E|]. eapply Forall_impl; [|exact Hf]. cbn; intros; lia.
    + apply Nat.leb_gt in E. constructor; [apply IH; exact Hl|].
      eapply Permutation_Forall; [symmetry; apply insertk_perm|].
      constructor; [cbn; lia | exact Hf].
Qed.

Lemma sortk_sorted l : StronglySorted Rk (sortk l).
Proof. induction l; cbn; [constructor | apply insertk_sorted; assumption]. Qed.

Lemma strongly_sorted_nth l d i j :
  StronglySorted Rk l -> i < j -> j < length l -> key (nth i l d) <= key (nth j l d).
Proof.
  revert i j; induction l as [|x l IH]; intros i j H hij hj; cbn in hj; [lia|].
  inversion H as [|? ? Hl Hf]; subst.
  destruct i, j; try lia; cbn.
  - rewrite Forall_forall in Hf. apply Hf, nth_In. lia.
  - apply IH; [exact Hl | lia | lia].
Qed.

(** In a sorted list, an element with a strictly smaller key comes first. *)
Lemma sorted_index_lt l d i j :
  StronglySorted Rk l -> i < length l -> j < length l ->
  key (nth j l d) < key (nth i l d) -> j < i.
Proof.
  intros H hi hj hk.
  destruct (Nat.lt_ge_cases j i) as [h|h]; [exact h|].
  destruct (Nat.eq_dec i j) as [->|hne]; [lia|].
  pose proof (strongly_sorted_nth l d i j H ltac:(lia) hj). lia.
Qed.

End SortByKey.
