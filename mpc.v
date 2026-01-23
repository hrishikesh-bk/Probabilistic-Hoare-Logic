Print Libraries.
From PHL Require Import Maps.
From PHL Require Import PHLTest.
From Coq Require Import Bool.
From Coq Require Import Arith.
From Coq Require Import EqNat.
From Coq Require Import PeanoNat. Import Nat.
From Coq Require Import Lia.
(*From PLF Require Export Imp.*)
(*From PLF Require Export Hoare.*)
From Coq Require Import Reals.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.
From Coq Require Import Init.Logic.
From Coq Require Import Lra.
From Coq Require Import String.
(* From Coq Require Import List. *)
Import Vector.VectorNotations.
From Coq Require Import Vector.
From Coq Require Import List String.
Import PHL.

Module MPC.


Definition test (x : string): Cmd:=
(KRoll x 2).


Definition r1:string := "r1". 
Definition r2:string := "r2".
Definition r3:string := "r3".
Definition x1:string := "x1".



Theorem DieTest: forall (p k: nat) (pr : R), (p > 0) -> (k >= 0) -> (k <= p) -> (pr = (INR p)) -> {{(prob true) = 1}}
<{ (r1 roll p) }>
{{ (prob (r1 = k))*(pr + 1) = 1 }}.
Proof.
intros. uncoerce_basic.
eapply HConseqLeft. Focus 2. apply HKRoll.
unfold PAImplies. unfold kroll_pt.  uncoerce_basic. simpl. intros.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l < k) -> 
              ((measure_sub_kroll_P r1 l (fst ps) (fun st : state => k = fst st r1) = 0)%R)).
- induct l. intros. unfold measure_sub_kroll_P. unfold measure_sub_k. unfold t_update. uncoerce_basic.
  replace (k = 0) with False. pose proof measure_true_dest (fst ps) {{true}}. simpl in H8. 
  replace False with (not True). lra. apply propositional_extensionality. easy. apply propositional_extensionality.
  split. intros. contradiction. lia. intros. simpl. assert (n < k) by lia. assert (n <= p) by lia.
  assert (n >= 0) by apply Nat.le_0_l. pose proof H4 H5 H11 H10 H9. rewrite H12.
  unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (k = S n) with (~True).
  pose proof measure_true_dest (fst ps) {{true}}. lra. apply propositional_extensionality. lia.

- assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l >= k) -> 
              ((measure_sub_kroll_P r1 l (fst ps) (fun st : state => k = fst st r1) = 1)%R)).
induct l.
 intros. simpl. unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (k = 0) with True.
  easy. apply propositional_extensionality. lia.
 intros. assert (n >= 0) by apply Nat.le_0_l. assert (n <= p) by lia. destruct (lt_dec n k) as [Hnk | Hnltk].
   * pose proof  (H4 n). pose proof H12 H6 H10 H11 Hnk. simpl. rewrite H13. unfold measure_sub_k. unfold t_update.
       uncoerce_basic. replace (k = S n) with True. lra. apply propositional_extensionality. lia.
   * assert (n >= k) by lia. pose proof H5 H6 H10 H11 H12. simpl. rewrite H13. unfold measure_sub_k.
      unfold t_update. uncoerce_basic. replace (k = S n) with False by (apply propositional_extensionality; lia).
      pose proof (measure_false_is_zero (fst ps)). rewrite H14. lra.
* pose proof (H5 p). assert (p >= 0) by apply Nat.le_0_l. assert (p <= p) by lia. assert (p >= k) by lia.
  pose proof H6 H H7 H8 H9. unfold measure_sub_kroll. rewrite H10. rewrite H2. rewrite plus_INR. rewrite INR_1.
  field_simplify. easy. assert (0 < p) by easy. pose proof lt_0_INR p H11. lra.
Qed.


Definition r11:string := "r11". 
Definition r12:string := "r12".
Definition r13:string := "r13".
(* Definition x1:string := "x1". *)

Definition r21:string := "r21". 
Definition r22:string := "r22".
Definition r23:string := "r23".
Definition x2:string := "x2".

Definition r31:string := "r31". 
Definition r32:string := "r32".
Definition r33:string := "r33".
Definition x3:string := "x3".

Definition s1f:string := "s1". 
Definition s2f:string := "s2".
Definition s3f:string := "s3".
Definition vf:string := "v".




Theorem MPCMain: forall (k1 l1 l2 : nat)  (p : nat), (p > 0) -> (k1 >= 0) -> (l1 >= 0) -> (l2 >= 0) -> (k1 < p) -> (l1 < p) -> (l2 < p) ->
 {{ (prob true) = 1 }}
<{
(r11 roll p);
((r12 roll p);
(r13 := ((x1 - r11 - r12) mod (p+1))))
}> 
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}.
Proof.
intros. set (pr := (1 / (INR (p + 1)))%R ). set (prinv := (INR (p + 1))).
eapply HSeq with (eta2 :=  {{ (prob ((x1 = k1) /\ (r11 = l1))) = 
       ((prob (x1 = k1)) * (prob ( r11 = l1) ))
      }}). Focus 2. eapply HSeq. Focus 2. apply HTAsgn.
simpl. unfold tasgn_pt. unfold measure_sub_term. uncoerce_basic. unfold assertion_sub_term. unfold t_update. simpl.
- eapply HConseqLeft. Focus 2. apply HKRoll. unfold kroll_pt. unfold PAImplies. intros. unfold measure_sub_kroll. simpl.
  replace  (measure_sub_kroll_P r12 p (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12))%R with 
        (((fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11)))%R.
  replace (measure_sub_kroll_P r12 p (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12))%R with 
       (fst ps (fun st : state => l1 = fst st r11))%R.
  replace (measure_sub_kroll_P r12 p (fst ps) (fun st : state => k1 = fst st x1)) with ( prinv *((fst ps) (fun st : state => k1 = fst st x1)))%R.
  unfold prinv. rewrite H6. field_simplify. easy. apply not_0_INR. lia. apply not_0_INR. lia.
 * assert (forall (q: nat), (measure_sub_kroll_P r12 q (fst ps) (fun st : state => k1 = fst st x1))%R
 = (INR (q + 1) * fst ps (fun st : state => k1 = fst st x1))%R).
  induct q. simpl. unfold measure_sub_k. unfold t_update. simpl. lra. intros. simpl (measure_sub_kroll_P r12 (S n) (fst ps) (fun st : state => k1 = fst st x1)). rewrite H7. unfold measure_sub_k. unfold t_update. 
 simpl (INR (n + 1) * fst ps (fun st : state => k1 = fst st x1) + fst ps (fun st : state => k1 = fst (fun x' : string => if (r12 =? x')%string
       then Teval (Const (S n)) st else fst st x', snd st) x1))%R. replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R. lra. rewrite <- S_INR. easy.
  unfold prinv. easy. 
Focus 2. 
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l < l2) -> 
              ((measure_sub_kroll_P r12 l (fst ps)  (fun st : state => l1 = fst st r11 /\ l2 = fst st r12) = 0)%R)).
 induct l. intros. unfold measure_sub_kroll_P. unfold measure_sub_k. unfold t_update. uncoerce_basic.
  replace (fun st : state => l1 = fst st r11 /\ l2 = 0) with (fun st : state => False). apply (measure_false_is_zero (fst ps)).
  apply functional_extensionality. intros. apply propositional_extensionality. lia. 
  intros. simpl. assert (n < l2) by lia. assert (n <= p) by lia.
  assert (n >= 0) by apply Nat.le_0_l. pose proof H7 H8 H14 H13 H12. rewrite H15.
  unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => l1 = fst st r11 /\ l2 = S n) with (fun st : state => False).
  rewrite (measure_false_is_zero (fst ps)). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l >= l2) -> 
              ((measure_sub_kroll_P r12 l (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12) = 
               (fst ps (fun st : state => l1 = fst st r11)))%R)).
 induct l. intros. simpl. unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => l1 = fst st r11 /\ l2 = 0) with (fun st : state => l1 = fst st r11).
 easy. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 intros. assert (n >= 0) by apply Nat.le_0_l. assert (n <= p) by lia. destruct (lt_dec n l2) as [Hnk | Hnltk].
 pose proof  (H7 n). simpl. pose proof H15 H9 H13 H14 Hnk. simpl. rewrite H16. unfold measure_sub_k. unfold t_update.
 uncoerce_basic. replace (fun st : state => l1 = fst st r11 /\ l2 = S n) with (fun st : state => l1 = fst st r11). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 assert (n >= l2) by lia. pose proof H8 H9 H13 H14 H15. simpl. rewrite H16. unfold measure_sub_k.
 unfold t_update. uncoerce_basic. replace (fun st : state => l1 = fst st r11 /\ l2 = S n) with (fun st : state => False) by (apply functional_extensionality; intros; apply propositional_extensionality; lia).
 pose proof (measure_false_is_zero (fst ps)). rewrite H17. lra.
 pose proof (H8 p). assert (p >= 0) by apply Nat.le_0_l. assert (p <= p) by lia. assert (p >= l2) by lia.
 pose proof H9 H H10 H11 H12. unfold measure_sub_kroll. rewrite H13. easy.

Focus 2.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l < l2) -> 
              ((measure_sub_kroll_P r12 l (fst ps)  (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12) = 0)%R)).
 induct l. intros. unfold measure_sub_kroll_P. unfold measure_sub_k. unfold t_update. uncoerce_basic.
  replace (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = 0) with (fun st : state => False). apply (measure_false_is_zero (fst ps)).
  apply functional_extensionality. intros. apply propositional_extensionality. lia. 
  intros. simpl. assert (n < l2) by lia. assert (n <= p) by lia.
  assert (n >= 0) by apply Nat.le_0_l. pose proof H7 H8 H14 H13 H12. rewrite H15.
  unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = S n) with (fun st : state => False).
  rewrite (measure_false_is_zero (fst ps)). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l >= l2) -> 
              ((measure_sub_kroll_P r12 l (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12) = 
               (fst ps (fun st : state => k1 = fst st x1 /\ l1 = fst st r11)))%R)).
 induct l. intros. simpl. unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = 0) with (fun st : state => k1 = fst st x1 /\ l1 = fst st r11).
 easy. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 intros. assert (n >= 0) by apply Nat.le_0_l. assert (n <= p) by lia. destruct (lt_dec n l2) as [Hnk | Hnltk].
 pose proof  (H7 n). simpl. pose proof H15 H9 H13 H14 Hnk. simpl. rewrite H16. unfold measure_sub_k. unfold t_update.
 uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = S n) with (fun st : state => k1 = fst st x1 /\ l1 = fst st r11). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 assert (n >= l2) by lia. pose proof H8 H9 H13 H14 H15. simpl. rewrite H16. unfold measure_sub_k.
 unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = S n) with (fun st : state => False) by (apply functional_extensionality; intros; apply propositional_extensionality; lia).
 pose proof (measure_false_is_zero (fst ps)). rewrite H17. lra.
 pose proof (H8 p). assert (p >= 0) by apply Nat.le_0_l. assert (p <= p) by lia. assert (p >= l2) by lia.
 pose proof H9 H H10 H11 H12. unfold measure_sub_kroll. rewrite H13. easy.

uncoerce_basic. eapply HConseqLeft. Focus 2. apply HKRoll. unfold kroll_pt. simpl. unfold pr. unfold PAImplies. intros.
unfold measure_sub_kroll. field_simplify.
assert ( (prinv * (measure_sub_kroll_P r11 p (fst ps)
        (fun st : state =>
         and (eq k1 (fst st x1)) (eq l1 (fst st r11))))%R)%R  = ((measure_sub_kroll_P r11 p (fst ps)
           (fun st : state => eq k1 (fst st x1))) * (measure_sub_kroll_P r11 p (fst ps)
        (fun st : state => eq l1 (fst st r11))))%R ). unfold prinv.
replace (measure_sub_kroll_P r11 p (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11)) with 
(((fst ps) (fun st : state => k1 = fst st x1)))%R.
replace (measure_sub_kroll_P r11 p (fst ps) (fun st : state => l1 = fst st r11))%R with 1%R.
replace (measure_sub_kroll_P r11 p (fst ps) (fun st : state => k1 = fst st x1)) 
 with (prinv * ((fst ps) (fun st : state => k1 = fst st x1)))%R. unfold prinv.
nra. unfold prinv.
assert (forall (q: nat), (measure_sub_kroll_P r11 q (fst ps) (fun st : state => k1 = fst st x1))%R
 = (INR (q + 1) * fst ps (fun st : state => k1 = fst st x1))%R).
- induct q. 
  * simpl. unfold measure_sub_k. unfold t_update. simpl. lra.
  * intros. simpl (measure_sub_kroll_P r11 (S n) (fst ps) (fun st : state => k1 = fst st x1)). rewrite H7. unfold measure_sub_k. unfold t_update. 
simpl (INR (n + 1) * fst ps (fun st : state => k1 = fst st x1) + fst ps (fun st : state => k1 = fst (fun x' : string => if (r11 =? x')%string
       then Teval (Const (S n)) st else fst st x', snd st) x1))%R. replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R.
lra. rewrite <- S_INR. easy.
- rewrite H7. easy.
- assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l < l1) -> 
              ((measure_sub_kroll_P r11 l (fst ps)  (fun st : state => l1 = fst st r11) = 0)%R)).
 induct l. intros. unfold measure_sub_kroll_P. unfold measure_sub_k. unfold t_update. uncoerce_basic.
  replace (l1 = 0) with (False). apply (measure_false_is_zero (fst ps)). apply propositional_extensionality. lia. 
  intros. simpl. assert (n < l1) by lia. assert (n <= p) by lia.
  assert (n >= 0) by apply Nat.le_0_l. pose proof H7 H8 H14 H13 H12. rewrite H15.
  unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (l1 = S n) with (False).
  rewrite (measure_false_is_zero (fst ps)). lra. apply propositional_extensionality. lia.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l >= l1) -> 
              ((measure_sub_kroll_P r11 l (fst ps) (fun st : state => l1 = fst st r11) = 
               1)%R)).
 induct l. intros. simpl. unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (l1 = 0) with (True).
 easy. apply propositional_extensionality. lia.
 intros. assert (n >= 0) by apply Nat.le_0_l. assert (n <= p) by lia. destruct (lt_dec n l1) as [Hnk | Hnltk].
 pose proof  (H7 n). simpl. pose proof H15 H9 H13 H14 Hnk. simpl. rewrite H16. unfold measure_sub_k. unfold t_update.
 uncoerce_basic. replace (l1 = S n) with (True). lra. apply propositional_extensionality. lia.
 assert (n >= l1) by lia. pose proof H8 H9 H13 H14 H15. simpl. rewrite H16. unfold measure_sub_k.
 unfold t_update. uncoerce_basic. replace (l1 = S n) with (False) by (apply propositional_extensionality; lia).
 pose proof (measure_false_is_zero (fst ps)). rewrite H17. lra.
 pose proof (H8 p). assert (p >= 0) by apply Nat.le_0_l. assert (p <= p) by lia. assert (p >= l1) by lia.
 pose proof H9 H H10 H11 H12. unfold measure_sub_kroll. rewrite H13. easy.

- assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l < l1) -> 
              ((measure_sub_kroll_P r11 l (fst ps)  (fun st : state => k1 = fst st x1 /\ l1 = fst st r11) = 0 )%R)).
 induct l. intros. unfold measure_sub_kroll_P. unfold measure_sub_k. unfold t_update. uncoerce_basic.
  replace (fun st : state => k1 = fst st x1 /\ l1 = 0) with (fun st : state => False). apply (measure_false_is_zero (fst ps)).
  apply functional_extensionality. intros. apply propositional_extensionality. lia. 
  intros. simpl. assert (n < l1) by lia. assert (n <= p) by lia.
  assert (n >= 0) by apply Nat.le_0_l. pose proof H7 H8 H14 H13 H12. rewrite H15.
  unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = S n) with (fun st : state => False).
  rewrite (measure_false_is_zero (fst ps)). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
assert (forall (l:nat), (p > 0) -> (l >= 0) -> (l <= p) -> (l >= l1) -> 
              ((measure_sub_kroll_P r11 l (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11) = 
               (fst ps (fun st : state => k1 = fst st x1)))%R)).
 induct l. intros. simpl. unfold measure_sub_k. unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = 0) with (fun st : state => k1 = fst st x1).
 easy. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 intros. assert (n >= 0) by apply Nat.le_0_l. assert (n <= p) by lia. destruct (lt_dec n l1) as [Hnk | Hnltk].
 pose proof  (H7 n). simpl. pose proof H15 H9 H13 H14 Hnk. simpl. rewrite H16. unfold measure_sub_k. unfold t_update.
 uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = S n) with (fun st : state => k1 = fst st x1). lra. apply functional_extensionality. intros. apply propositional_extensionality. lia.
 assert (n >= l1) by lia. pose proof H8 H9 H13 H14 H15. simpl. rewrite H16. unfold measure_sub_k.
 unfold t_update. uncoerce_basic. replace (fun st : state => k1 = fst st x1 /\ l1 = S n) with (fun st : state => False) by (apply functional_extensionality; intros; apply propositional_extensionality; lia).
 pose proof (measure_false_is_zero (fst ps)). rewrite H17. lra.
 pose proof (H8 p). assert (p >= 0) by apply Nat.le_0_l. assert (p <= p) by lia. assert (p >= l1) by lia.
 pose proof H9 H H10 H11 H12. unfold measure_sub_kroll. rewrite H13. easy.
- unfold prinv in H7. rewrite <- H7. field_simplify. lra. apply not_0_INR. lia. apply not_0_INR. lia.
-  apply not_0_INR. lia. 
- apply not_0_INR. lia.
Qed.

(*
Definition r21:string := "r21". 
Definition r22:string := "r22".
Definition r23:string := "r23".
Definition x2:string := "x2". *)


Definition MainVars := (r11 :: r12:: r13:: x1:: nil).

Theorem MPCSub: forall (k1 l1 l2 : nat)  (p : nat) (ri1 ri2 ri3 xi: string), (p > 0) -> (k1 >= 0) -> (l1 >= 0) -> (l2 >= 0) -> (k1 < p) -> (l1 < p) -> (l2 < p) ->
 (NoDup (ri1 :: ri2 :: ri3 :: xi :: nil)) -> (~ In ri1 MainVars) -> (~ In ri2  MainVars) -> (~ In ri3 MainVars) -> (~ In xi MainVars) ->
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}
<{
(ri1 roll p);
((ri2 roll p);
(ri3 := ((xi - ri1 - ri2) mod (p+1))))
}> 
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}.
Proof.

intros. set (pr := (1 / (INR (p + 1)))%R ). set (prinv := (INR (p + 1))).
 assert (forall (rij: string) (l: nat) (ps: Pstate), (l > 0) -> (~ In rij MainVars) ->
              ((measure_sub_kroll_P rij l (fst ps)  (fun st : state => l1 = fst st r11 /\ l2 = fst st r12))%R = 
                ((INR (l+1)) * ((fst ps)  (fun st : state => l1 = fst st r11 /\ l2 = fst st r12))))%R).
   induct l. intros. easy. intros. assert (rij <> r11) by (intro; apply H13; simpl; auto). assert (rij <> r12) by (intro; apply H13; simpl; auto).
   assert (forall th : nat,
   ((fun st : state => l1 = (if (rij =? r11)%string then th else fst st r11) /\ l2 = (if (rij =? r12)%string then th else fst st r12)) 
      = (fun st : state => l1 = (fst st r11) /\ l2 = (fst st r12)))) as Hlpr. pose proof (String.eqb_neq rij r11). apply proj2 in H16. pose proof H16 H14. rewrite H17.
    pose proof (String.eqb_neq rij r12). apply proj2 in H18. pose proof H18 H15. rewrite H19. intros. easy.
    destruct (gt_dec n 0) as [Hnk | Hnltk].
    pose proof H11 ps Hnk H13. simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    rewrite H16. unfold measure_sub_k. unfold t_update. simpl (INR (n + 1) * fst ps (fun st : state => l1 = fst st r11 /\ l2 = fst st r12) + fst ps
   (fun st : state => l1 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r11 /\ l2 = fst
    (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r12))%R. rewrite (Hlpr (S n)).
    replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R. lra. rewrite <- S_INR. easy.
    simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    replace n with 0. simpl. unfold measure_sub_k. unfold t_update. simpl. rewrite (Hlpr 0). rewrite (Hlpr 1).
    lra. lia. 

assert (forall (rij: string) (l: nat) (ps: Pstate), (l > 0) -> (~ In rij MainVars) ->
              ((measure_sub_kroll_P rij l (fst ps)  (fun st : state => l1 = fst st r11 /\ l2 = fst st r12))%R = 
                ((INR (l+1)) * ((fst ps)  (fun st : state => l1 = fst st r11 /\ l2 = fst st r12))))%R).
   induct l. intros. easy. intros. assert (rij <> r11) by (intro; apply H14; simpl; auto). assert (rij <> r12) by (intro; apply H14; simpl; auto).
   assert (forall th : nat,
   ((fun st : state => l1 = (if (rij =? r11)%string then th else fst st r11) /\ l2 = (if (rij =? r12)%string then th else fst st r12)) 
      = (fun st : state => l1 = (fst st r11) /\ l2 = (fst st r12)))) as Hlpr. pose proof (String.eqb_neq rij r11). apply proj2 in H17. pose proof H17 H15. rewrite H18.
    pose proof (String.eqb_neq rij r12). apply proj2 in H19. pose proof H19 H16. rewrite H20. intros. easy.
    destruct (gt_dec n 0) as [Hnk | Hnltk].
    pose proof H12 ps Hnk H14. simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    rewrite H17. unfold measure_sub_k. unfold t_update. simpl (INR (n + 1) * fst ps (fun st : state => l1 = fst st r11 /\ l2 = fst st r12) + fst ps
   (fun st : state => l1 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r11 /\ l2 = fst
    (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r12))%R. rewrite (Hlpr (S n)).
    replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R. lra. rewrite <- S_INR. easy.
    simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    replace n with 0. simpl. unfold measure_sub_k. unfold t_update. simpl. rewrite (Hlpr 0). rewrite (Hlpr 1). lra. lia.

 assert (forall (rij: string) (l: nat) (ps: Pstate),(l > 0) -> (~In rij MainVars) -> 
    ((measure_sub_kroll_P rij l (fst ps) (fun st : state => k1 = fst st x1))%R = ((INR (l+1)) * ((fst ps) (fun st : state => k1 = fst st x1)))%R)).
 induct l. intros. easy. intros. assert (rij <> x1) by (intro; apply H15; simpl; auto).
   assert (forall th : nat,
   ((fun st : state => k1 = (if (rij =? x1)%string then th else fst st x1))
      = (fun st : state => k1 = (fst st x1)))) as Hlpr. pose proof (String.eqb_neq rij x1). apply proj2 in H17. pose proof H17 H16. rewrite H18.
    pose proof (String.eqb_neq rij x1). apply proj2 in H19. pose proof H19 H16. easy.
    destruct (gt_dec n 0) as [Hnk | Hnltk].
    pose proof H13 ps Hnk H15. simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => k1 = fst st x1)).
    rewrite H17. unfold measure_sub_k. unfold t_update. simpl (INR (n + 1) * fst ps (fun st : state => k1 = fst st x1) + fst ps
    (fun st : state => k1 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) x1))%R. rewrite (Hlpr (S n)).
    replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R. lra. rewrite <- S_INR. easy.
    simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    replace n with 0. simpl. unfold measure_sub_k. unfold t_update. simpl. rewrite (Hlpr 0). rewrite (Hlpr 1).
    lra. lia.

 assert (forall (rij: string) (l: nat) (ps: Pstate),(l > 0) -> (~In rij MainVars) -> 
    ((measure_sub_kroll_P rij l (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12))%R = ((INR (l+1)) * ((fst ps) (fun st : state =>
    k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12)))%R)).
 induct l. intros. easy. intros. assert (rij <> x1) by (intro; apply H16; simpl; auto). assert (rij <> r11) by (intro; apply H16; simpl; auto). assert (rij <> r12) by (intro; apply H16; simpl; auto).
   assert (forall th : nat,
   ((fun st : state =>
    k1 = (if (rij =? x1)%string then th else fst st x1) /\
    l1 = (if (rij =? r11)%string then th else fst st r11) /\
    l2 = (if (rij =? r12)%string then th else fst st r12))
  =  (fun st : state => k1 = (fst st x1) /\ l1 = (fst st r11) /\ l2 = (fst st r12)))) as Hlpr. 
  pose proof (String.eqb_neq rij x1). apply proj2 in H20. pose proof H20 H17. rewrite H21.
  pose proof (String.eqb_neq rij r11). apply proj2 in H22. pose proof H22 H18. rewrite H23.
  pose proof (String.eqb_neq rij r12). apply proj2 in H24. pose proof H24 H19. rewrite H25. easy.
    destruct (gt_dec n 0) as [Hnk | Hnltk].
    pose proof H14 ps Hnk H16. simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12)).
    rewrite H20. unfold measure_sub_k. unfold t_update. simpl (INR (n + 1) * fst ps (fun st : state => k1 = fst st x1 /\ l1 = fst st r11 /\ l2 = fst st r12) +
 fst ps
   (fun st : state =>
    k1 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) x1 /\
    l1 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r11 /\
    l2 = fst (fun x' : string => if (rij =? x')%string then Teval (Const (S n)) st else fst st x', snd st) r12))%R. rewrite (Hlpr (S n)).
    replace (INR (S n + 1))%R with  ((INR (n + 1)) + 1)%R. lra. rewrite <- S_INR. easy.
    simpl (measure_sub_kroll_P rij (S n) (fst ps) (fun st : state => l1 = fst st r11 /\ l2 = fst st r12)).
    replace n with 0. simpl. unfold measure_sub_k. unfold t_update. simpl. rewrite (Hlpr 0). rewrite (Hlpr 1).
    lra. lia.

(* main proof *)
uncoerce_basic. 
apply HSeq with (eta2 := {{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}).
uncoerce_basic. eapply HConseqLeft. Focus 2.  apply HKRoll. unfold PAImplies. intros. unfold kroll_pt. unfold measure_sub_kroll. simpl.
rewrite (H12 ri1 p ps H H7). rewrite (H13 ri1 p ps H H7). rewrite (H14 ri1 p ps H H7). rewrite H15. field_simplify. lra.
apply not_0_INR. lia. apply not_0_INR. lia.

uncoerce_basic.
apply HSeq with (eta2 := {{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}).
uncoerce_basic. eapply HConseqLeft. Focus 2.  apply HKRoll. unfold PAImplies. intros. unfold kroll_pt. unfold measure_sub_kroll. simpl.
rewrite (H12 ri2 p ps H H8). rewrite (H13 ri2 p ps H H8). rewrite (H14 ri2 p ps H H8). rewrite H15. field_simplify. lra.
apply not_0_INR. lia. apply not_0_INR. lia.
    
uncoerce_basic. eapply HConseqLeft. Focus 2. apply HTAsgn.
unfold PAImplies. intros. simpl. unfold tasgn_pt. unfold measure_sub_term. uncoerce_basic. unfold assertion_sub_term. unfold t_update. simpl.
assert (ri3 <> r11) by (intro; apply H9; simpl; auto). assert (ri3 <> r12) by (intro; apply H9; simpl; auto).
assert (ri3 <> x1) by (intro; apply H9; simpl; auto).
replace  (fun st : state =>
   k1 = (if (ri3 =? x1)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st x1) /\
   l1 = (if (ri3 =? r11)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st r11) /\
   l2 = (if (ri3 =? r12)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st r12)) with 
  (fun st : state => k1 = (fst st x1) /\ l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq ri3 x1). apply proj2 in H19. pose proof H19 H18. rewrite H20.
pose proof (String.eqb_neq ri3 r11). apply proj2 in H21. pose proof H21 H16. rewrite H22.
pose proof (String.eqb_neq ri3 r12). apply proj2 in H23. pose proof H23 H17. rewrite H24.
easy.
replace (fun st : state => k1 = (if (ri3 =? x1)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st x1))
with (fun st : state => k1 = (fst st x1)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq ri3 x1). apply proj2 in H19. pose proof H19 H18. rewrite H20.
easy.
replace (fun st : state => l1 = (if (ri3 =? r11)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st r11) /\
         l2 = (if (ri3 =? r12)%string then (fst st xi - fst st ri1 - fst st ri2) mod (p + 1) else fst st r12))
with (fun st : state => l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros.
pose proof (String.eqb_neq ri3 r11). apply proj2 in H19. pose proof H19 H16. rewrite H20.
pose proof (String.eqb_neq ri3 r12). apply proj2 in H21. pose proof H21 H17. rewrite H22.
easy.
easy.
Qed.

Theorem MPC2ndLoop: forall (k1 l1 l2 : nat)  (p : nat) (r1i r2i r3i si: string), (p > 0) -> (k1 >= 0) -> (l1 >= 0) -> (l2 >= 0) -> (k1 < p) -> (l1 < p) -> (l2 < p) ->
 (NoDup (r1i :: r2i :: r3i :: si :: nil)) -> (~ In si MainVars) ->
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}
<{
(si := ((r1i + r2i + r3i) mod (p+1)))
}> 
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}.
Proof.
intros. uncoerce_basic.
eapply HConseqLeft. Focus 2. apply HTAsgn. unfold PAImplies. intros. unfold tasgn_pt. unfold measure_sub_term. uncoerce_basic. 
unfold assertion_sub_term. unfold t_update. simpl.
assert (si <> r11) by (intro; apply H7; simpl; auto). assert (si <> r12) by (intro; apply H7; simpl; auto).
assert (si <> x1) by (intro; apply H7; simpl; auto).
replace (fun st : state =>
   k1 = (if (si =? x1)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st x1) /\
   l1 = (if (si =? r11)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st r11) /\
   l2 = (if (si =? r12)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st r12)) 
with (fun st : state => k1 = (fst st x1) /\ l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq si x1). apply proj2 in H12. pose proof H12 H11. rewrite H13.
pose proof (String.eqb_neq si r11). apply proj2 in H14. pose proof H14 H9. rewrite H15.
pose proof (String.eqb_neq si r12). apply proj2 in H16. pose proof H16 H10. rewrite H17.
easy.
replace (fun st : state => k1 = (if (si =? x1)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st x1))
with (fun st : state => k1 = (fst st x1)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq si x1). apply proj2 in H12. pose proof H12 H11. rewrite H13.
easy.
replace (fun st : state => l1 = (if (si =? r11)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st r11) /\
    l2 = (if (si =? r12)%string then (fst st r1i + fst st r2i + fst st r3i) mod (p + 1) else fst st r12))
with (fun st : state => l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros.
pose proof (String.eqb_neq si r11). apply proj2 in H12. pose proof H12 H9. rewrite H13.
pose proof (String.eqb_neq si r12). apply proj2 in H14. pose proof H14 H10. rewrite H15.
easy. 
easy.
Qed.

Theorem MPCFinalAssign:  forall (k1 l1 l2 : nat)  (p : nat) (s1 s2 s3 v: string), (p > 0) -> (k1 >= 0) -> (l1 >= 0) -> (l2 >= 0) -> (k1 < p) -> (l1 < p) -> (l2 < p) ->
 (NoDup (s1 :: s2 :: s3 :: v :: nil)) -> (~ In s1 MainVars) -> (~ In s2  MainVars) -> (~ In s3 MainVars) -> (~ In v MainVars) ->
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}
<{
(v := ((s1 + s2 + s3) mod (p+1)))
}> 
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}.
Proof.
intros. uncoerce_basic.
eapply HConseqLeft. Focus 2. apply HTAsgn. unfold PAImplies. intros.  unfold tasgn_pt. unfold measure_sub_term. uncoerce_basic.
unfold assertion_sub_term. unfold t_update. simpl.
assert (v <> r11) by (intro; apply H10; simpl; auto). assert (v <> r12) by (intro; apply H10; simpl; auto).
assert (v <> x1) by (intro; apply H10; simpl; auto).
replace   (fun st : state =>
   k1 = (if (v =? x1)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st x1) /\
   l1 = (if (v =? r11)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st r11) /\
   l2 = (if (v =? r12)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st r12))
with (fun st : state => k1 = (fst st x1) /\ l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq v x1). apply proj2 in H15. pose proof H15 H14. rewrite H16.
pose proof (String.eqb_neq v r11). apply proj2 in H17. pose proof H17 H12. rewrite H18.
pose proof (String.eqb_neq v r12). apply proj2 in H19. pose proof H19 H13. rewrite H20.
easy.
replace (fun st : state => k1 = (if (v =? x1)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st x1))
with (fun st : state => k1 = (fst st x1)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq v x1). apply proj2 in H15. pose proof H15 H14. rewrite H16. easy.
replace (fun st : state => l1 = (if (v =? r11)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st r11) /\
    l2 = (if (v =? r12)%string then (fst st s1 + fst st s2 + fst st s3) mod (p + 1) else fst st r12))
with (fun st : state => l1 = (fst st r11) /\ l2 = (fst st r12)).
Focus 2. apply functional_extensionality. intros. pose proof (String.eqb_neq v r11). apply proj2 in H15. pose proof H15 H12. rewrite H16.
pose proof (String.eqb_neq v r12). apply proj2 in H17. pose proof H17 H13. rewrite H18. easy.
easy.
Qed.




Theorem MPCFull: forall (k1 l1 l2 : nat)  (p : nat), (p > 0) -> (k1 >= 0) -> (l1 >= 0) -> (l2 >= 0) -> (k1 < p) -> (l1 < p) -> (l2 < p) ->
 {{ (prob true) = 1 }}
<{
((r11 roll p);
((r12 roll p);
(r13 := ((x1 - r11 - r12) mod (p+1)))));

((r21 roll p);
((r22 roll p);
(r23 := ((x2 - r21 - r22) mod (p+1)))));

((r31 roll p);
((r32 roll p);
(r33 := ((x3 - r31 - r32) mod (p+1)))));

((s1f := ((r11 + r21 + r31) mod (p+1)));
(s2f := ((r12 + r22 + r32) mod (p+1)));
(s3f := ((r13 + r23 + r33) mod (p+1))));

(vf := ((s1f + s2f + s3f) mod (p+1)))

}> 
{{ (prob ((x1 = k1) /\ (r11 = l1) /\ (r12 = l2))) = ((prob (x1 = k1))* (prob ((r11 = l1) /\ (r12 = l2))))}}.
Proof.

Print MPCMain.
intros. eapply HSeq. apply (MPCMain k1 l1 l2 p). easy. easy. easy. easy. easy. easy. easy.
eapply HSeq. apply (MPCSub k1 l1 l2 p).  easy. easy. easy. easy. easy. easy. easy. 
repeat constructor; simpl; intuition discriminate. simpl. intuition discriminate.
simpl. intuition discriminate. simpl. intuition discriminate. simpl. intuition discriminate.
eapply HSeq. apply (MPCSub k1 l1 l2 p).  easy. easy. easy. easy. easy. easy. easy. 
repeat constructor; simpl; intuition discriminate. simpl. intuition discriminate.
simpl. intuition discriminate. simpl. intuition discriminate. simpl. intuition discriminate.
eapply HSeq. eapply HSeq. apply (MPC2ndLoop k1 l1 l2 p). easy. easy. easy. easy. easy. easy. easy. 
repeat constructor; simpl; intuition discriminate. simpl. intuition discriminate.
eapply HSeq. apply (MPC2ndLoop k1 l1 l2 p). easy. easy. easy. easy. easy. easy. easy. 
repeat constructor; simpl; intuition discriminate. simpl. intuition discriminate.
apply (MPC2ndLoop k1 l1 l2 p). easy. easy. easy. easy. easy. easy. easy. 
repeat constructor; simpl; intuition discriminate. simpl. intuition discriminate.
apply (MPCFinalAssign k1 l1 l2 p s1f s2f s3f vf).  easy. easy. easy. easy. easy. easy. easy.
repeat constructor; simpl; intuition discriminate.  simpl. intuition discriminate.
simpl. intuition discriminate. simpl. intuition discriminate. simpl. intuition discriminate.
Qed.



End MPC.
