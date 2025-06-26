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
From Coq Require Import Notations.
Import PHL.

Locate Even.
Check Even.
Print Even.
Print even_spec.
Print even.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Lemma even_oddS : forall n : nat, Even n -> Odd (S n).
Proof. intros. unfold Odd. unfold Even in H. inversion H. exists x0. rewrite H0. lia.
Qed.

Lemma odd_evenS : forall n : nat, Odd n -> Even (S n).
Proof. intros. unfold Even. unfold Odd in H. inversion H. exists (x0 + 1)%nat. rewrite H0. lia.
Qed.

Lemma evenb_dec : forall n,
  {Even n} + {Odd n}.
Proof. intro. induction n.
(*   induction n as [| [| n'] IH]. *)
  - left. unfold Even. assert (0 = 2 * 0)%nat. lia. exists 0. apply H. 
  - destruct IHn.
    + right. apply even_oddS. apply e. 
    + left. apply odd_evenS. apply o.
Qed.

(* Theorem even_2k: forall n : nat, even n -> exists k:nat, (n = (2*k))%nat.
Proof. intro. induction n. *)

(* Inductive Even : nat -> Prop :=
| Even_O : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).

Inductive Odd : nat -> Prop :=
| Odd_1 : Odd 1
| Odd_SS : forall n, Odd n -> Odd (S (S n)).

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => Datatypes.true
  | 1 => Datatypes.false
  | S (S n') => evenb n'
  end.

Lemma even_not_odd: forall n, Even n -> ~ Odd n.
Proof. intro. induction n.
  + 

Lemma even_Sodd : forall n, Even n -> Odd (S n).
Proof. intro. induction n. 
  + intro. constructor. 
  + intro. 

Lemma evenb_dec : forall n,
  {Even n} + {Odd n}.
Proof. intro. induction n.
(*   induction n as [| [| n'] IH]. *)
  - left. constructor.
  - right. constructor.
  - destruct IH.
    + left. now constructor.
    + right. now constructor.
Qed. *) 

Definition b : string := "b".
Definition val : string := "val".
Definition y1 : string := "y1".
Definition y2 : string := "y2".
(* Open Scope com_scope.
Open Scope passertion_scope.
Open Scope hoare_spec_scope. *)

Check Cmd.

Definition example_prog1: Cmd :=
  TAsgn b 1.
Definition half : R := 0.5.

Definition body : Cmd :=
  <{ 
  b toss 0.5;
  if b then val := 2 * val + 1 else val := 2 * val end
}>.

Fixpoint uniform_exp (k : nat) : Cmd :=
  match k with 
    | O => Skip
    | S n => CSeq (uniform_exp n) body
end.

Compute uniform_exp 2.

Theorem asgn2k_1 : forall (k : nat) (r : R), {{ ((prob (val = k)) = (0.5*r)) /\ y1 = (0.5*r)}}
        val := 2*val {{(prob (val = (2*k))) = y1}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val}> {{(prob (val = (2*k))) = y1}}) (TAsgn val <{2*val}>) ({{(prob (val = (2*k))) = y1}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = (0.5*r)) /\ y1 = (0.5*r)}}) (tasgn_pt val <{2*val}> {{(prob (val = (2*k))) = y1}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl.
                 replace ((fun st : state => (k + (k + 0))%nat = (val !-> (fst st val + (fst st val + 0))%nat; fst st) val)) with ((fun st : state => k = fst st val)).
                 transitivity ((0.5 * r)%R). apply H. symmetry. apply H.
                  apply functional_extensionality. intros. rewrite t_update_eq. apply propositional_extensionality.
                  split. lia. lia.
              * exact T1.
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k_0 : forall (k : nat) (r : R), {{ ((prob (val = k)) = (0.5*r)) /\ y1 = 0}}
        val := 2*val {{(prob (val = (2*k + 1))) = y1}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val}> {{(prob (val = (2*k + 1))) = y1}}) (TAsgn val <{2*val}>) ({{(prob (val = (2*k + 1))) = y1}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = (0.5*r)) /\ y1 = 0}}) (tasgn_pt val <{2*val}> {{(prob (val = (2*k + 1))) = y1}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl.
(*  assert (fst ps (fun st : state => ~ (k = fst st val)) = 0%R).
                        apply measure_P_eq_true. apply H. replace (snd ps y1) with 0%R. *) 
                      assert (((fst ps
   (fun st : state =>
    (((k + (k + 0)) + 1)%nat) = ((val !-> ((fst st val) + ((fst st val) + 0))%nat; (fst st)) val))) = (fst ps (fun st : state => False)))%R).
    apply equivalence. unfold Assertion_equiv. intro. split. replace ((val !-> (fst st val + (fst st val + 0))%nat; fst st) val) with ((fst st val + (fst st val + 0))%nat).
    assert ((k + (k + 0) + 1)%nat <> (fst st val + (fst st val + 0))%nat). lia. apply H0. rewrite t_update_eq. reflexivity. easy.
    rewrite empty_set_measure in H0. transitivity (0%R). apply H0. symmetry. apply H.
              * exact T1. 
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k1_1 : forall (k : nat) (r : R), {{ ((prob (val = k)) = (0.5*r)) /\ y2 = (0.5*r)}}
        val := 2*val + 1 {{(prob (val = (2*k + 1))) = y2}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k + 1))) = y2}}) (TAsgn val <{2*val + 1}>) ({{(prob (val = (2*k + 1))) = y2}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = (0.5*r)) /\ y2 = (0.5*r)}}) (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k + 1))) = y2}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl.
                 replace ((fun st : state => (k + (k + 0) + 1)%nat = (val !-> (fst st val + (fst st val + 0) + 1)%nat; fst st) val)) with ((fun st : state => k = fst st val)).
                 transitivity ((0.5*r)%R). apply H. symmetry. apply H.
                  apply functional_extensionality. intros. rewrite t_update_eq. apply propositional_extensionality.
                  split. lia. lia.
              * exact T1.
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k1_0 : forall (k : nat) (r : R), {{ ((prob (val = k)) = (0.5*r)) /\ y2 = 0}}
        val := 2*val + 1 {{(prob (val = (2*k))) = y2}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k))) = y2}}) (TAsgn val <{2*val + 1}>) ({{(prob (val = (2*k))) = y2}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = (0.5*r)) /\ y2 = 0}}) (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k))) = y2}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl. 
                assert (((fst ps
   (fun st : state =>
    ((k + (k + 0))%nat) = ((val !-> (((fst st val) + ((fst st val) + 0)) + 1)%nat; (fst st)) val))) = (fst ps (fun st : state => False)))%R).
            apply equivalence. unfold Assertion_equiv. intro. split. rewrite t_update_eq. assert ((k + (k + 0))%nat <> (fst st val + (fst st val + 0) + 1)%nat).
            lia. apply H0. easy. rewrite empty_set_measure in H0. transitivity (0%R). apply H0. symmetry. apply H.
              * exact T1. 
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem ifthenpre1: forall (k: nat) (r : R), {{(((prob (val = k)) = (0.5*r)) /\ y2 = (0.5*r)) / (b) \ (((prob (val = k)) = (0.5*r)) /\ y1 = 0) }}
  <{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k + 1)))}}.
Proof. intros. eapply HIfThen.
        - simpl. eapply HConseq. 
          * apply PAImpliesItself.
          * assert (T: PAImplies ({{(prob (val = (2*k + 1))) = y2}}) ({{ y2 = (prob (val = (2*k + 1)))}})).
            unfold PAImplies. intros. symmetry. apply H. apply T.
          * apply asgn2k1_1.
        - simpl. eapply HConseq. 
          * apply PAImpliesItself.
          * assert (T: PAImplies ({{(prob (val = (2*k + 1))) = y1}}) ({{ y1 = (prob (val = (2*k + 1)))}})).
            unfold PAImplies. intros. symmetry. apply H. apply T.
          * apply asgn2k_0.
Qed.

Theorem ifthenpre0: forall (k: nat) (r : R), {{(((prob (val = k)) = (0.5*r)) /\ y2 = 0) / (b) \ (((prob (val = k)) = (0.5*r)) /\ y1 = (0.5*r)) }}
  <{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k)))}}.
Proof. intros. eapply HIfThen.
        - simpl. eapply HConseq. 
          * apply PAImpliesItself.
          * assert (T: PAImplies ({{(prob (val = (2*k))) = y2}}) ({{ y2 = (prob (val = (2*k)))}})).
            unfold PAImplies. intros. symmetry. apply H. apply T.
          * apply asgn2k1_0.
        - simpl. eapply HConseq. 
          * apply PAImpliesItself.
          * assert (T: PAImplies ({{(prob (val = (2*k))) = y1}}) ({{ y1 = (prob (val = (2*k)))}})).
            unfold PAImplies. intros. symmetry. apply H. apply T.
          * apply asgn2k_1.
Qed.

Theorem intermediate0: forall (k : nat) (r : R), {{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)) /\ y2 = 0) /\ y1 = (0.5*r)}}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k)))}}.
Proof. intros. eapply HConseq with (eta2 := {{(((prob (val = k)) = (0.5*r)) /\ y2 = 0) / (b) \ (((prob (val = k)) = (0.5*r)) /\ y1 = (0.5*r)) }}).
        + easy.
        + apply PAImpliesItself.
        + apply ifthenpre0.
Qed. 

Theorem intermediate1: forall (k : nat) (r : R), {{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)) /\ y2 = (0.5*r)) /\ y1 = 0}}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k + 1)))}}.
Proof. intros. eapply HConseq with (eta2 := {{(((prob (val = k)) = (0.5*r)) /\ y2 = (0.5*r)) / (b) \ (((prob (val = k)) = (0.5*r)) /\ y1 = 0) }}).
        + easy. 
        + apply PAImpliesItself.
        + apply ifthenpre1.
Qed.

Theorem eliminate_y1_0: forall (k : nat) (r : R), {{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)) /\ y2 = 0)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ (y2 + (0.5*r)) = (prob (val = (2*k)))}}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)) /\ y2 = 0)}}) y1 (0.5*r)%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + y1) = (prob (val = (2*k)))}}) y1 (0.5*r)%R).
       + easy.
       + easy.
       + apply eliminate_y.
          * easy. 
          * easy.
          * apply intermediate0.
Qed.

Theorem eliminate_y2_0: forall (k : nat) (r : R), {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{  (0.5*r) = (prob (val = (2*k)))}}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)))}}) y2 0%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + (0.5*r)) = (prob (val = (2*k)))}}) y2 0%R).
       + easy. 
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_eq in H. replace (0 + (0.5 * r))%R with (0.5*r)%R in H. apply H. lra.
       + apply eliminate_y.
          * easy. 
          * easy.
          * apply eliminate_y1_0.
Qed.

Theorem eliminate_y1_1: forall (k : nat) (r : R), {{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)) /\ y2 = (0.5*r))}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ (y2 + 0) = (prob (val = (2*k+1)))}}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r) ) /\ y2 = (0.5*r))}}) y1 0%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + y1) = (prob (val = (2*k + 1)))}}) y1 0%R).
       + easy.
       + easy.
       + apply eliminate_y.
          * easy.
          * easy.
          * apply intermediate1.
Qed.

Theorem eliminate_y2_1: forall (k : nat) (r : R), {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{  (0.5*r) = (prob (val = (2*k+1)))}}.
Proof. intros. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)))}}) y2 (0.5*r)%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + 0) = (prob (val = (2*k+1)))}}) y2 (0.5*r)%R).
       + easy.
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_eq in H. replace (0.5*r + 0)%R with (0.5*r)%R in H. apply H. lra. 
       + apply eliminate_y.
          * easy.
          * easy.
          * apply eliminate_y1_1.
Qed.

Theorem tossb: forall (k : nat) (r : R), {{ (prob (val = k)) = r}}
b toss 0.5  {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}}.
Proof. intros. eapply HConseq with (eta2 := btoss_pt b 0.5 ({{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}})).
        + unfold PAImplies. intro. unfold Pteval. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp.
          unfold assertion_sub_bexp. unfold CBoolexp_of_bexp. unfold CTermexp_of_Texp. unfold CTermexp_of_nat.
          unfold Teval. unfold Beval. unfold PTerm_of_R. replace (1 - 0.5)%R with (0.5)%R. simpl.
          replace ((fun st : state => k = fst st val /\ (b !-> True; snd st) b)) with (fun st : state => k = fst st val). 
          replace ((fun st : state => k = fst st val /\ (b !-> False; snd st) b)) with (fun st : state => False).
          replace ((fun st : state => k = fst st val /\ ~ (b !-> True; snd st) b)) with (fun st : state => False). 
          replace ((fun st : state => k = fst st val /\ ~ (b !-> False; snd st) b)) with (fun st : state => k = fst st val).  
          * intros. split. 
            - rewrite empty_set_measure. lra.
            - rewrite empty_set_measure. lra.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * lra.
        + apply PAImpliesItself.
        + apply HBToss.
Qed.

Theorem body1: forall (k : nat) (r : R), {{ (prob (val = k)) = r}}
body {{  0.5*r = (prob (val = (2*k+1)))}}.
Proof. intros. eapply HSeq with (eta2:= {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}}).
        + apply tossb.
        + apply eliminate_y2_1.
Qed.

Theorem body2: forall (k : nat) (r : R), {{ (prob (val = k)) = r}}
body {{  0.5*r = (prob (val = (2*k)))}}.
Proof. intros. eapply HSeq with (eta2:= {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)}}).
        + apply tossb.
        + apply eliminate_y2_0.
Qed.


Theorem asgn_t0 : {{ (prob true) = 0.5 /\ y2 = 0.5}} val := 2*val {{y2 = (prob true) }}.
Proof. apply HConseqLeft with (eta2 := tasgn_pt val <{ 2*val }> {{y2 = (prob true) }}).
        + intro. unfold tasgn_pt. simpl. unfold measure_sub_term. intro. transitivity (0.5%R). easy. unfold measure_sub_term. easy.
        + apply HTAsgn. 
Qed. 

Theorem asgn_t1 : {{ (prob true) = 0.5 /\ y1 = 0.5 }} val := 2*val + 1 {{y1 = (prob true)}}.
Proof. apply HConseqLeft with (eta2 := tasgn_pt val <{ 2*val + 1 }> {{y1 = (prob true)}}). 
        + intro. unfold tasgn_pt. simpl. unfold measure_sub_term. intro. transitivity (0.5%R). easy. unfold measure_sub_term. easy.
        + apply HTAsgn.
Qed.

Theorem ifthen_t : {{(((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) /\ y1 = 0.5) /\ y2 = 0.5 }}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ y1 + y2 = (prob true) }}.
Proof. apply HConseqLeft with (eta2 := {{ (prob true) = 0.5 /\ y1 = 0.5 / (b) \  (prob true) = 0.5 /\ y2 = 0.5}} ).
        + easy.
        + apply HIfThen.
            - apply asgn_t1.
            - apply asgn_t0.
Qed. 

Theorem elimy2_t : {{(((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) /\ y1 = 0.5) }}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ y1 + 0.5 = (prob true) }}.
Proof. apply HConseq with (eta2:= eta_update_y_p ({{(((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) /\ y1 = 0.5)}}) y2 (0.5%R))
                          (eta3:= eta_update_y_p ({{ y1 + y2 = (prob true) }}) y2 (0.5%R)).
        + easy.
        + easy.
        + apply eliminate_y. easy. easy. apply ifthen_t.
Qed.

Theorem elimy1_t : {{((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) }}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ 1 = (prob true) }}.
Proof. apply HConseq with (eta2:= eta_update_y_p ({{((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5)}}) y1 (0.5%R))
                          (eta3:= eta_update_y_p ({{ y1 + 0.5 = (prob true) }}) y1 (0.5%R)).
        + easy.
        + intro. unfold eta_update_y_p. simpl. unfold pstate_update. unfold PTerm_of_R. rewrite t_update_eq. lra. 
        + apply eliminate_y. easy. easy. apply elimy2_t.
Qed.

Theorem tosst : {{(prob true) = 1}} <{ b toss 0.5 }>  {{((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) }}.
Proof. apply HConseqLeft with (eta2 := btoss_pt b 0.5 {{((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) }}).
        + intro. unfold btoss_pt. simpl. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. unfold Beval.
          unfold PTerm_of_R. simpl. replace (1 - 0.5)%R with (0.5%R).
          replace (fun st : state => True /\ ((b !-> True; (snd st)) b)) with (fun st : state => True).
          replace (fun st : state => True /\ ((b !-> False; (snd st)) b)) with (fun st : state => False ).
          replace (fun st : state => True /\ (~ ((b !-> True; (snd st)) b))) with (fun st : state => False). 
          replace (fun st : state => True /\ (~ ((b !-> False; (snd st)) b))) with (fun st : state => True ). 
          * intro. rewrite empty_set_measure. split. lra. lra.
          * apply functional_extensionality. intro. apply propositional_extensionality. rewrite t_update_eq. tauto.
          * apply functional_extensionality. intro. apply propositional_extensionality. rewrite t_update_eq. tauto.
          *  apply functional_extensionality. intro. apply propositional_extensionality. rewrite t_update_eq. tauto.
          *  apply functional_extensionality. intro. apply propositional_extensionality. rewrite t_update_eq. tauto.
          * lra.
        + apply HBToss.
Qed.

Theorem bodyt : {{ (prob true) = 1}} body {{(prob true) = 1}}.
Proof. apply HSeq with (eta2 := {{((prob (true /\ b)) = 0.5 /\ (prob (true /\ ~ b)) = 0.5) }}).
        + apply tosst.
        + apply HConseqRight with (eta2 := {{1 = (prob true) }}). easy. apply elimy1_t.
Qed.
 
Theorem uniform_exp_true : forall (k : nat), hoare_triple ({{(prob true) = 1}}) (uniform_exp k) ({{(prob true) = 1}}).
Proof. induction k.
        + apply HSkip.
        + apply HSeq with (eta2 := {{(prob true) = 1}}).
          - easy.
          - apply bodyt.
Qed.




Definition twok (k : nat) : R := 1 / (pow 2 k). 

Definition post_st (k1 : nat) : Assertion := fun st => (fst st) val = k1.
Definition post (k k1 : nat) : PAssertion := fun ps => fst ps (post_st k1) = (twok k).



Lemma mult_half : forall k : nat,
  ((1 / 2) * (1 / (pow 2 k)))%R = (1 / (pow 2 (S k)))%R.
Proof.
  intros k. simpl.
  unfold Rdiv.
  field.
  apply pow_nonzero.
  lra.
Qed.

Theorem unif: forall (k k1 : nat), (k1 < (2 ^ k)) -> hoare_triple ({{(prob (val = 0)) = 1}}) (uniform_exp k) (post k k1).
Proof. intro k. induction k.
    + intros. destruct k1.
      - unfold post. unfold uniform_exp. unfold twok. unfold post_st. apply HConseqRight with (eta2:= {{(prob (val = 0)) = 1}}). 
        * replace (1 / 2 ^ 0)%R with (1%R). unfold Pteval. unfold CTermexp_of_Texp. unfold CTermexp_of_nat. unfold Teval. unfold PTerm_of_R.
          unfold PAImplies. intros. replace (fun st : state => fst st val = 0) with (fun st : state => 0 = fst st val). easy.
          apply functional_extensionality. intro. apply propositional_extensionality. easy. lra. 
        * apply HSkip.
      - exfalso. assert (~ (S k1 < 2 ^ 0)). replace (2 ^ 0) with 1. lia. simpl. reflexivity. contradiction.
    + simpl. intros. destruct (evenb_dec k1).
      - unfold Even in e. inversion e. apply HSeq with (eta2 := (post k x0)). apply IHk. lia.
        unfold post. unfold twok. unfold post_st. rewrite H0. apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => (fst st val) = (2*x0)%nat)) = ((0.5*(1 / (2 ^ k)))%R))).
        unfold PAImplies.  intros. replace ((1 / (2 ^ (S k)))%R) with ((0.5 * (1 / (2 ^ k)))%R).
        apply H1. 
        * replace 0.5%R with (1/2)%R. apply mult_half. lra.
        * apply HConseq with (eta2:= (fun st : Pstate =>
     eq
       (Pteval
          (Pint
             (fun st0 : state => eq (CTermexp_of_nat x0 st0) (CTermexp_of_Texp (Var val) st0)))
          st) (PTerm_of_R (Rdiv 1 (pow 2 k)) st))) (eta3 := (fun st : Pstate =>
     eq (Rmult (PTerm_of_R 0.5 st) (PTerm_of_R (Rdiv 1 (pow 2 k)) st))
       (Pteval
          (Pint
             (fun st0 : state =>
              eq (mul (CTermexp_of_nat 2 st0) (CTermexp_of_nat x0 st0))
                (CTermexp_of_Texp (Var val) st0))) st))).
          ** unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold PTerm_of_R. unfold Teval. unfold Pteval. unfold PAImplies. intros.
             replace (fun st0 : state => x0 = (fst st0 val)) with (fun st0 : state => (fst st0 val) = x0).
             apply H1. apply functional_extensionality. intro. apply propositional_extensionality. easy. 
          ** unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold PTerm_of_R. unfold Teval. unfold Pteval. unfold PAImplies. intros. 
             replace (fun st : state => (fst st val) = ((2 * x0)%nat)) with (fun st : state => ((2 * x0)%nat) = (fst st val)). symmetry.
             apply H1. apply functional_extensionality. intro. apply propositional_extensionality. easy.
          ** apply body2.
        - unfold Odd in o. inversion o. apply HSeq with (eta2 := (post k x0)). apply IHk. lia.
        unfold post. unfold twok. unfold post_st. rewrite H0. apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => (fst st val) = ((2*x0)+1)%nat)) = ((0.5*(1 / (2 ^ k)))%R))).
        unfold PAImplies.  intros. replace ((1 / (2 ^ (S k)))%R) with ((0.5 * (1 / (2 ^ k)))%R).
        apply H1. 
        * replace 0.5%R with (1/2)%R. apply mult_half. lra.
        * apply HConseq with (eta2:= (fun st : Pstate =>
     eq
       (Pteval
          (Pint
             (fun st0 : state => eq (CTermexp_of_nat x0 st0) (CTermexp_of_Texp (Var val) st0)))
          st) (PTerm_of_R (Rdiv 1 (pow 2 k)) st)))
     (eta3 := (fun st : Pstate =>
     eq (Rmult (PTerm_of_R 0.5 st) (PTerm_of_R (Rdiv 1 (pow 2 k)) st))
       (Pteval
          (Pint
             (fun st0 : state =>
              eq (add (mul (CTermexp_of_nat 2 st0) (CTermexp_of_nat x0 st0))
                   (CTermexp_of_nat 1 st0))
                (CTermexp_of_Texp (Var val) st0))) st))).
          ** unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold PTerm_of_R. unfold Teval. unfold Pteval. unfold PAImplies. intros.
             replace (fun st0 : state => x0 = (fst st0 val)) with (fun st0 : state => (fst st0 val) = x0).
             apply H1. apply functional_extensionality. intro. apply propositional_extensionality. easy. 
          ** unfold CTermexp_of_nat. unfold CTermexp_of_Texp. unfold PTerm_of_R. unfold Teval. unfold Pteval. unfold PAImplies. intros. 
             replace (fun st : state => (fst st val) = (((2 * x0)+1)%nat)) with (fun st : state => (((2 * x0)+1)%nat) = (fst st val)). symmetry.
             apply H1. apply functional_extensionality. intro. apply propositional_extensionality. easy.
          ** apply body1.
Qed.

Definition post1 (k k1 : nat) := fun ps: Pstate => (fst ps) (fun st : state => (fst st) val < k1) = ((INR k1) / (2 ^ k))%R.

Theorem unif_sum: forall (k k1 : nat), (k1 <= 2 ^ k) -> hoare_triple ({{(prob (val = 0)) = 1}}) (uniform_exp k) (post1 k k1).
Proof. intros k k1. induction k1. intro. apply HConseqRight with (eta2 := post k 0).
      - unfold PAImplies. intro. unfold post1. unfold Z.of_nat. replace (fst ps (fun st : state => (fst st val) < 0)) with (fst ps {{false}}).
        rewrite empty_set_measure. intro. simpl. lra. apply equivalence. easy.
      - apply unif. assert  (2^k <> 0). apply Nat.pow_nonzero. lia. lia.
      - intro. apply HConseqRight with (eta2 := (fun ps: Pstate => ((post1 k k1) ps) /\ ((post k k1) ps))).
        + unfold PAImplies. intro. unfold post1. unfold post. unfold post_st. intro.
          replace (fst ps (fun st : state => (fst st val) < (S k1))) with (fst ps (fun st : state => (fst st val) < k1 \/ (fst st val) = k1)).
          rewrite <- fin_additivity. unfold twok in H0. 
          replace (fst ps (fun st : state => (fst st val) < k1)) with (((INR k1) / (2 ^ k))%R).
          replace (fst ps (fun st : state => (fst st val) = k1)) with  ((1 / (2 ^ k))%R). unfold Rdiv. Search (?a*?c + ?b*?c)%R.
          rewrite <- Rmult_plus_distr_r. Search (?a*?c = ?b*?c)%R. apply Rmult_eq_compat_r. Search "INR". rewrite <- INR_1. rewrite <- plus_INR.
          replace (k1 + 1)%nat with (S k1). reflexivity. lia. 
          symmetry. apply H0. symmetry. apply H0. 
          intro. lia. apply equivalence. unfold Assertion_equiv. intro. lia. 
        + eapply HAnd. apply IHk1. lia. apply unif. lia.
Qed.

Theorem unif_full : forall (k : nat), hoare_triple ({{(prob (val = 0)) = 1}}) (uniform_exp k) (fun ps => fst ps (fun st => fst st val < 2^k) = 1%R).
Proof. intro. apply HConseqRight with (eta2 := (post1 k (2^k))).
        + intro. unfold post1. replace (((INR (2 ^ k)) / (2 ^ k))%R) with (1%R). tauto. rewrite pow_INR.
          replace (INR 2) with (2%R). Search "Rdiv". symmetry. apply Rdiv_diag. apply pow_nonzero. lra. easy.
        + apply unif_sum. easy.
Qed.

Theorem unif_empty : forall (k : nat), hoare_triple ({{(prob (val = 0)) = 1 /\ (prob true) = 1 }}) (uniform_exp k) (fun ps : Pstate => fst ps (fun st => fst st val >= 2^k) = 0%R).
Proof. intro. apply HConseqRight with (eta2 := (fun ps : Pstate => fst ps (fun st => fst st val < 2^k) = 1%R /\ fst ps {{true}} = 1%R)).
        + intro. replace (fst ps {{true}}) with ((fst ps (fun st => (fst st val) < (2 ^ k) \/ (fst st val) >= (2 ^ k)))).
          * intro. rewrite <- fin_additivity in H. lra. intro. lia.  
          * apply equivalence. unfold Assertion_equiv. intro. lia.
        + apply HAnd.
          * apply HConseqLeft with (eta2 := ({{(prob (val = 0)) = 1}})).
            ** easy.
            ** apply unif_full.
          * apply HConseqLeft with (eta2 := ({{(prob true) = 1}})).
            ** easy.
            ** apply uniform_exp_true.
Qed.

Theorem unif_ge: forall (k k1: nat), (k1 <= 2^k) -> hoare_triple ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}) (uniform_exp k) (fun ps => fst ps (fun st => fst st val >= k1) = (1 - ((INR k1) / 2^k))%R).
Proof. intros. apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps) (fun st => (fst st val) < k1) = ((INR k1) / (2 ^ k))%R /\ fst ps (fun st => fst st val < 2^k) = 1%R /\ fst ps (fun st => fst st val >= 2^k) = 0%R)).
          + intro. intro. replace (fun st : state => (fst st val) >= k1) with (fun st : state => ((fst st val) >= k1 /\ (fst st val) < 2^k) \/ ((fst st val) >= 2^k) ).
            * rewrite <- fin_additivity. replace (fst ps (fun st : state => ((fst st val) >= (2 ^ k))%nat)) with (0%R).
              Search "plus_0". rewrite Rplus_0_r. replace (fst ps (fun st : state => ((fst st val) >= k1) /\ ((fst st val) < (2 ^ k)))) with (fst ps (fun st : state => ((fst st val) < (2 ^ k)) /\ ~((fst st val) < k1))).
              -  rewrite measure_AnotB. replace (fst ps (fun st : state => ((fst st val) < (2 ^ k))%nat)) with (1%R).
                 replace (fst ps (fun st : state => (((fst st val) < (2 ^ k))%nat) /\ (((fst st val) < k1)%nat))) with ((INR k1) / (2 ^ k))%R.
                 reflexivity. symmetry. transitivity (fst ps (fun st : state => (fst st val) < k1)).
                 apply equivalence. intro. lia. apply H0. symmetry. apply H0.
              - apply equivalence. intro. lia.
              - easy.
              - intro. lia.
            * apply functional_extensionality. intro. apply propositional_extensionality. lia.
          + apply HAnd.
            * apply HConseqLeft with (eta2 := {{(prob (val = 0)) = 1}}). easy. apply unif_sum. apply H.
            * apply HAnd.
              -  apply HConseqLeft with (eta2 := {{(prob (val = 0)) = 1}}). easy. apply unif_full.
              - apply unif_empty.
Qed.

Definition body_unif_k (k : nat) : Cmd :=
(CSeq (TAsgn val (Const 0)) (uniform_exp k)).

Definition uniform_k (k : nat) : Cmd :=
  While (Leq (Const k) (Var val)) (body_unif_k k).

Theorem body_unif_k_t : forall (k : nat), hoare_triple ({{(prob true) = 1}}) (body_unif_k k) ({{(prob true) = 1}}).
Proof. intro. apply HSeq with (eta2 := ({{(prob true) = 1}})).
        + apply HConseq with (eta2 := tasgn_pt val <{0}> ({{ (prob (val = 0))= 1 /\ ((prob true) = 1)}}))
                              (eta3 := ({{ (prob (val = 0))= 1 /\ ((prob true) = 1)}})).
          * intro. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. unfold Pteval.
            simpl. unfold CTermexp_of_nat. unfold PTerm_of_R. intro. split. transitivity (fst ps {{true}}). 
            apply equivalence. unfold Assertion_equiv. intro. rewrite t_update_eq. lia. easy. easy.
          * easy.
          * apply HTAsgn.
        + apply uniform_exp_true.
Qed.

Definition post_body_t (k k1 : nat) : PAssertion := fun ps: Pstate => (fst ps (fun st : state => (((fst st) val) >= k)%nat) <=  (1 - ((INR k) / 2^k)))%R /\ ((fst ps (fun st : state => ~ (k <= ((fst st) val))%nat /\ True)) <= (INR k/ 2 ^ k))%R.

Theorem body_unif_t_prop: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (val >= k)) = 1 /\ (prob (val >= k)) = (prob true) }}) (body_unif_k k) (post_body_t k k1).
Proof. intros. apply HAnd. 
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn.
          * apply HConseqRight with (eta2 := (fun ps : Pstate => fst ps (fun st => fst st val >= k) = (1 - ((INR k) / 2^k))%R)).
            ** intro. intro. apply Req_le. apply H0.
            ** apply unif_ge. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0.
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn. 
          * apply HConseq with (eta2 :=  {{(prob (val = 0)) = 1}}) (eta3 := (post1 k k)).
            ** intro. easy.
            ** unfold post. unfold post_st. unfold twok. intro. intros. 
               right. unfold post1 in H0. transitivity (fst ps (fun st : state => (fst st val) < k)).
                apply equivalence. unfold Assertion_equiv. intro. lia. easy. 
            ** apply unif_sum. Search (?a < ?b)%nat. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0. 
Qed.

Definition post_body_LB_t (k k1 : nat): PAssertion := fun ps: Pstate => (fst ps (fun st : state => (((fst st) val) >= k)%nat) >=  (1 - ((INR k) / 2^k)))%R /\ (fst ps (fun st : state => ~ (k <= ((fst st) val))%nat /\ True) >= (INR k/ 2 ^ k))%R.

Theorem body_unif_prop_LB_t : forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (val >= k)) = 1 /\ (prob (val >= k)) = (prob true) }}) (body_unif_k k) (post_body_LB_t k k1).
Proof. intros. apply HAnd. 
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn.
          * apply HConseqRight with (eta2 := (fun ps : Pstate => fst ps (fun st => fst st val >= k) = (1 - ((INR k) / 2^k))%R)).
            ** intro. intro. apply Req_ge. apply H0.
            ** apply unif_ge. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0.
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn. 
          * apply HConseq with (eta2 :=  {{(prob (val = 0)) = 1}}) (eta3 := (post1 k k)).
            ** intro. easy.
            ** intro. intros. 
               right. unfold post1 in H0. transitivity (fst ps (fun st : state => (fst st val) < k)).
                apply equivalence. unfold Assertion_equiv. intro. lia. easy.  
            ** apply unif_sum. Search (?a < ?b)%nat. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0. 
Qed.

Theorem uniform_k_UB_inter_t : forall (k k1 : nat) (b : bexp) (tempA : Assertion), 
        (b = (Leq (Const k) (Var val))) -> Assertion_equiv tempA (CBoolexp_of_bexp (Leq (Const k) (Var val))) -> (k1 < k) ->
         hoare_triple ({{(prob (b /\ tempA)) <= y1 /\ (prob (b /\ tempA)) = (prob true) }}) (While b (body_unif_k k)) (fun ps : Pstate => (fst ps (fun st : state => True) <= 1*(snd ps y1))%R).
Proof. intros. eapply HWhileUB with (m := 1) (G := [(fun st1 => Beval b0 st1)]) (P := [([(1 - ((INR k) / 2^k))%R])]) (T := [(INR k /2^k)%R]) (X := [1%R]).
        + intro. simpl. tauto. 
        + intros. destruct i. 
          * simpl. unfold int_true_eq_one. unfold apply_func. unfold inner_conj_leq. simpl. unfold gamma_leq. unfold gamma_compare. simpl.
            rewrite H. unfold Beval. unfold Teval. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval.
            replace (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) <= (1 - ((INR k) / (2 ^ k))))%R) /\
    True) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ True)) <= ((INR k) / (2 ^ k)))%R)) with 
      (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) <= (1 - ((INR k) / (2 ^ k))))%R)) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ True)) <= ((INR k) / (2 ^ k)))%R)).
            apply body_unif_t_prop with (k1 := k1). apply H1. apply functional_extensionality. intro. apply propositional_extensionality. tauto.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * unfold lin_ineq. simpl. rewrite Rplus_0_r. Search "minus". Search "Ropp". Search "Rplus_comm". rewrite Rplus_comm. rewrite Rmult_1_r. rewrite Rplus_minus_assoc. rewrite Rplus_minus_l. lra.
          * assert (~ (S i) < 1). lia. contradiction.
        + assert (0 < 1). lia. exact H2.
        + intro. simpl. rewrite H. unfold Beval. unfold Teval. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0.
          unfold Beval in H0. unfold Teval in H0. symmetry. apply H0.
        + simpl. lra. 
Qed. 

Theorem uniform_k_LB_inter_t : forall (k k1 : nat) (b : bexp) (tempA : Assertion), 
        (b = (Leq (Const k) (Var val))) -> Assertion_equiv tempA (CBoolexp_of_bexp (Leq (Const k) (Var val))) -> (k1 < k) ->
        hoare_triple ({{(prob (b /\ tempA)) >= y1 /\ (prob (b /\ tempA)) = (prob true) }}) (While b (body_unif_k k)) (fun ps : Pstate => ((1*(snd ps y1)) <= fst ps (fun st : state => True))%R).
Proof. intros. eapply HWhileLB with (m := 1) (G := [(fun st1 => Beval b0 st1)]) (P := [([(1 - ((INR k) / 2^k))%R])]) (T := [(INR k/2^k)%R]) (X := [(1)%R]).
        + intros i T st. destruct i.
          * simpl. tauto. 
          * assert (~ (S i) < 1). lia. contradiction. 
        + intros. destruct i. 
          *  assert (~ (j < 0)). lia. contradiction.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i.
          * simpl. left. apply Rdiv_pos_pos. apply lt_0_INR. lia.  
            assert (forall (n : nat), (2^n > 0)%R). induction n. simpl. lra. simpl. rewrite <- Rmult_0_r with (r := 2%R). apply Rmult_lt_compat_l.
            lra. apply IHn. apply H3.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * simpl. unfold int_true_eq_one. unfold apply_func. unfold inner_conj_geq. simpl. unfold gamma_geq. unfold gamma_compare. simpl.
            rewrite H. unfold Beval. unfold Teval. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. 
            replace (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) >= (1 - ((INR k) / (2 ^ k))))%R) /\
    True) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ True)) >= ((INR k) / (2 ^ k)))%R)) with 
      (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) >= (1 - ((INR k) / (2 ^ k))))%R)) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ True)) >= ((INR k) / (2 ^ k)))%R)).
            apply body_unif_prop_LB_t with (k1 := k1). apply H1. apply functional_extensionality. intro. apply propositional_extensionality. tauto.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * unfold lin_ineq_lb. simpl. rewrite Rplus_0_r. Search "minus". Search "Ropp". rewrite Rmult_minus_distr_r. rewrite Rmult_1_l. rewrite <- Rplus_minus_swap. rewrite Rmult_1_r. rewrite Rplus_minus_r. lra. 
          * assert (~ (S i) < 1). lia. contradiction.
        + assert (0 < 1). lia. exact H2.
        + intro. simpl. rewrite H. unfold Beval. unfold Teval. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0.
          unfold Beval in H0. unfold Teval in H0. symmetry. apply H0.
        + simpl. lra. 
Qed.

Theorem uniform_k_inter_t: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}) (uniform_k k) (fun ps : Pstate => ((1*(snd ps y1)) = fst ps (fun st : state => True))%R).
Proof. intros. apply HConseqLeft with (eta2 := (fun st : Pstate =>
     (((Pteval
          (Pint
             (fun st0 : state =>
              (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0) /\
              (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0))) st) =
       (PTermexp_of_pterm (Pvar y1) st))%R) /\
     ((Pteval
         (Pint
            (fun st0 : state =>
             (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0) /\
             (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0))) st) =
      (Pteval (Pint (fun st0 : state => True)) st)))).
        + simpl. intro. intro. replace (fun st0 : state => ((k <= (fst st0 val))%nat) /\ ((k <= (fst st0 val))%nat)) with (fun st0 : state => ((k <= (fst st0 val))%nat)).
          unfold CTermexp_of_nat in H0. easy. apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => True) <= (1*(snd ps y1)))%R /\ ((1*(snd ps y1)) <= fst ps (fun st : state => True))%R)).
          * intro. lra.
          * apply HAnd.
            - apply HConseqLeft with (eta2:= ({{(prob ((k <= val) /\ (k <= val))) <= y1 /\ (prob ((k <= val) /\ (k <= val))) = (prob true) }})).
              -- intro. intro. split. apply Req_le. easy. easy.
              -- apply uniform_k_UB_inter_t with (b := (Leq (Const k) (Var val))) (tempA := (CBoolexp_of_bexp (Leq (Const k) (Var val)))) (k1 := k1).
                  reflexivity. easy. easy.
            - apply HConseqLeft with (eta2:= ({{(prob ((k <= val) /\ (k <= val))) >= y1 /\ (prob ((k <= val) /\ (k <= val))) = (prob true) }})).
               -- intro. intro. split. apply Req_le. easy. easy.
              -- apply uniform_k_LB_inter_t with (k1 := k1) (b := (Leq (Const k) (Var val))) (tempA := (CBoolexp_of_bexp (Leq (Const k) (Var val)))).
                  reflexivity. easy. easy.
Qed.

Theorem uniform_t: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob  (k = val)) = 1 /\ (prob (k = val)) = (prob true)}}) (uniform_k k)  (fun ps : Pstate => ((1 = fst ps (fun st : state => True))%R)).
Proof. intros. apply HConseqLeft with (eta2 := {{(prob (k <= val)) = 1 /\ (prob (k <= val)) = (prob true) }}).
        + intro. unfold Pteval. unfold CTermexp_of_Texp. unfold CTermexp_of_nat. unfold Teval. unfold PTerm_of_R. intro.
          assert (fst ps {{true}} = 1%R). transitivity (fst ps (fun st : state => (fst st val) = k)). easy. easy.
          rewrite H1. split. 
          * apply Rle_antisym. 
            - rewrite <- H1. apply measure_inclusion. easy.
            - destruct H0. rewrite <- H0. apply measure_inclusion. intros. Search "eq_le" in Nat. apply eq_le_incl. symmetry. easy. 
          * apply Rle_antisym. 
            - rewrite <- H1. apply measure_inclusion. easy.
            - destruct H0. rewrite <- H0. apply measure_inclusion. intros. Search "eq_le" in Nat. apply eq_le_incl. symmetry. easy.
       + apply HConseq with (eta2 := eta_update_y_p ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}) y1 (1%R))
                            (eta3 := eta_update_y_p (fun ps : Pstate => ((1*(snd ps y1)) = fst ps (fun st : state => True))%R) y1 (1%R) ).
          * intro. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. simpl. intro.
            split. rewrite t_update_eq. easy. easy.
          * unfold eta_update_y_p. unfold pstate_update. unfold Pteval. simpl. intro. rewrite t_update_eq. lra.
          * apply eliminate_y. easy. easy. apply HConseqLeft with (eta2 := ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }})).
             - intro. easy.
             - apply uniform_k_inter_t with (k1 := k1). apply H.
Qed.





Definition post_body (k k1 : nat): PAssertion := fun ps: Pstate => (fst ps (fun st : state => (((fst st) val) >= k)%nat) <=  (1 - ((INR k) / 2^k)))%R /\ (fst ps (fun st : state => ~ (k <= ((fst st) val))%nat /\ ((fst st) val) = k1) <= (1/ 2 ^ k))%R.

Theorem body_unif_prop: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (val >= k)) = 1 /\ (prob (val >= k)) = (prob true) }}) (body_unif_k k) (post_body k k1).
Proof. intros. apply HAnd. 
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn.
          * apply HConseqRight with (eta2 := (fun ps : Pstate => fst ps (fun st => fst st val >= k) = (1 - ((INR k) / 2^k))%R)).
            ** intro. intro. apply Req_le. apply H0.
            ** apply unif_ge. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0.
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn. 
          * apply HConseq with (eta2 :=  {{(prob (val = 0)) = 1}}) (eta3 := (post k k1)).
            ** intro. easy.
            ** unfold post. unfold post_st. unfold twok. intro. intros. 
               replace (fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) with (fst ps (fun st : state => (fst st val) = k1)).
               right. apply H0. apply equivalence. intro. split. intro. split. lia. apply H1. tauto.
            ** apply unif. Search (?a < ?b)%nat. apply lt_le_trans with (m := k). easy. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0. 
Qed. 

Definition post_body_LB (k k1 : nat): PAssertion := fun ps: Pstate => (fst ps (fun st : state => (((fst st) val) >= k)%nat) >=  (1 - ((INR k) / 2^k)))%R /\ (fst ps (fun st : state => ~ (k <= ((fst st) val))%nat /\ ((fst st) val) = k1) >= (1/ 2 ^ k))%R.

Theorem body_unif_prop_LB : forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (val >= k)) = 1 /\ (prob (val >= k)) = (prob true) }}) (body_unif_k k) (post_body_LB k k1).
Proof. intros. apply HAnd. 
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn.
          * apply HConseqRight with (eta2 := (fun ps : Pstate => fst ps (fun st => fst st val >= k) = (1 - ((INR k) / 2^k))%R)).
            ** intro. intro. apply Req_ge. apply H0.
            ** apply unif_ge. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0.
        + apply HSeq with (eta2 := {{(prob (val = 0)) = 1 /\ (prob true) = 1}}).
          * apply HConseqLeft with (eta2 := (tasgn_pt val <{0}> ({{(prob (val = 0)) = 1 /\ (prob true) = 1}}))).
            ** intro. unfold tasgn_pt. unfold measure_sub_term. unfold Pteval. unfold PTerm_of_R. unfold CTermexp_of_nat. unfold CTermexp_of_Texp.
               unfold Teval. unfold assertion_sub_term. unfold Teval. simpl. intro. replace (fst ps (fun st : state => 0 = ((val !-> 0; (fst st)) val))) with (fst ps {{true}}).
               split. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. transitivity (fst ps (fun st : state => (k <= (fst st val))%nat))%R. symmetry. apply H0.   
               apply H0. apply equivalence. intro. rewrite t_update_eq. lia.
            ** apply HTAsgn. 
          * apply HConseq with (eta2 :=  {{(prob (val = 0)) = 1}}) (eta3 := (post k k1)).
            ** intro. easy.
            ** unfold post. unfold post_st. unfold twok. intro. intros. 
               replace (fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) with (fst ps (fun st : state => (fst st val) = k1)).
               right. apply H0. apply equivalence. intro. split. intro. split. lia. apply H1. tauto.
            ** apply unif. Search (?a < ?b)%nat. apply lt_le_trans with (m := k). easy. assert (forall n : nat, n <= 2^n). induction n.
                - lia.
                - Search "Nat". destruct n. simpl. lia. apply le_trans with (m := (2 * (S n))%nat). simpl. lia. 
                  apply le_trans with (m := (2 * (2 ^ (S n)))%nat). Search (?a*?b <= ?a*?c). apply mul_le_mono_l. apply IHn.
                  simpl. lia.
                - apply H0. 
Qed.

Theorem uniform_k_UB_inter : forall (k k1 : nat) (b : bexp) (tempA : Assertion), 
        (b = (Leq (Const k) (Var val))) -> Assertion_equiv tempA (CBoolexp_of_bexp (Leq (Const k) (Var val))) -> (k1 < k) ->
         hoare_triple ({{(prob (b /\ tempA)) <= y1 /\ (prob (b /\ tempA)) = (prob true) }}) (While b (body_unif_k k)) (fun ps : Pstate => (fst ps (fun st : state => ((fst st) val) = k1) <= ((1/INR k)*(snd ps y1)))%R).
Proof. intros. eapply HWhileUB with (m := 1) (G := [(fun st1 => Beval b0 st1)]) (P := [([(1 - ((INR k) / 2^k))%R])]) (T := [(1/2^k)%R]) (X := [(1/INR k)%R]).
        + intro. simpl. tauto. 
        + intros. destruct i. 
          * simpl. unfold int_true_eq_one. unfold apply_func. unfold inner_conj_leq. simpl. unfold gamma_leq. unfold gamma_compare. simpl.
            rewrite H. unfold Beval. unfold Teval. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. 
            replace (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) <= (1 - ((INR k) / (2 ^ k))))%R) /\
    True) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) <=
     (1 / (2 ^ k)))%R)) with 
      (fun ps : Pstate =>
   (((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) <= (1 - ((INR k) / (2 ^ k))))%R) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) <=
     (1 / (2 ^ k)))%R)).
            apply body_unif_prop. apply H1. apply functional_extensionality. intro. apply propositional_extensionality. tauto.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * unfold lin_ineq. simpl. rewrite Rplus_0_r. Search "minus". Search "Ropp". rewrite Rmult_minus_distr_r. rewrite Rmult_1_l. rewrite -> Rdiv_1_l. replace ((INR k) / (2 ^ k))%R with ((INR k)*  (/ (2 ^ k)))%R.
            rewrite Rmult_inv_r_id_m. rewrite Rdiv_1_l. rewrite Rplus_comm. rewrite Rplus_minus. apply Rle_refl. 
            Search INR. rewrite <- INR_0. Search INR. apply not_INR. Search (?q <> 0). apply neq_0_lt_0. Search (0 < ?a) in Nat. apply lt_lt_0 with (n := k1). apply H1. rewrite Rdiv_def. reflexivity.
          * assert (~ (S i) < 1). lia. contradiction.
        + assert (0 < 1). lia. exact H2.
        + intro. simpl. rewrite H. unfold Beval. unfold Teval. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0.
          unfold Beval in H0. unfold Teval in H0. symmetry. apply H0.
        + simpl. rewrite Rdiv_def. reflexivity.
Qed. 

Theorem uniform_k_LB_inter : forall (k k1 : nat) (b : bexp) (tempA : Assertion), 
        (b = (Leq (Const k) (Var val))) -> Assertion_equiv tempA (CBoolexp_of_bexp (Leq (Const k) (Var val))) -> (k1 < k) ->
        hoare_triple ({{(prob (b /\ tempA)) >= y1 /\ (prob (b /\ tempA)) = (prob true) }}) (While b (body_unif_k k)) (fun ps : Pstate => (((1/INR k)*(snd ps y1)) <= fst ps (fun st : state => ((fst st) val) = k1))%R).
Proof. intros. eapply HWhileLB with (m := 1) (G := [(fun st1 => Beval b0 st1)]) (P := [([(1 - ((INR k) / 2^k))%R])]) (T := [(1/2^k)%R]) (X := [(1/INR k)%R]).
        + intros i T st. destruct i.
          * simpl. tauto. 
          * assert (~ (S i) < 1). lia. contradiction. 
        + intros. destruct i. 
          *  assert (~ (j < 0)). lia. contradiction.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i.
          * simpl. left. apply Rdiv_pos_pos. lra. Search "pow_nonzero". 
            assert (forall (n : nat), (2^n > 0)%R). induction n. simpl. lra. simpl. rewrite <- Rmult_0_r with (r := 2%R). apply Rmult_lt_compat_l.
            lra. apply IHn. apply H3.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * simpl. unfold int_true_eq_one. unfold apply_func. unfold inner_conj_geq. simpl. unfold gamma_geq. unfold gamma_compare. simpl.
            rewrite H. unfold Beval. unfold Teval. unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold Teval. 
            replace (fun ps : Pstate =>
   ((((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) >= (1 - ((INR k) / (2 ^ k))))%R) /\
    True) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) >=
     (1 / (2 ^ k)))%R)) with 
      (fun ps : Pstate =>
   (((fst ps (fun st1 : state => (k <= (fst st1 val))%nat)) >= (1 - ((INR k) / (2 ^ k))))%R) /\
   (((fst ps (fun st : state => (~ ((k <= (fst st val))%nat)) /\ ((fst st val) = k1))) >=
     (1 / (2 ^ k)))%R)).
            apply body_unif_prop_LB. apply H1. apply functional_extensionality. intro. apply propositional_extensionality. tauto.
          * assert (~ (S i) < 1). lia. contradiction.
        + intros. destruct i. 
          * unfold lin_ineq_lb. simpl. rewrite Rplus_0_r. Search "minus". Search "Ropp". rewrite Rmult_minus_distr_r. rewrite Rmult_1_l. rewrite -> Rdiv_1_l. replace ((INR k) / (2 ^ k))%R with ((INR k)*  (/ (2 ^ k)))%R.
            rewrite Rmult_inv_r_id_m. rewrite Rdiv_1_l. rewrite Rplus_comm. rewrite Rplus_minus. apply Rle_refl. 
            Search INR. rewrite <- INR_0. Search INR. apply not_INR. Search (?q <> 0). apply neq_0_lt_0. apply lt_lt_0 with (n := k1). apply H1. rewrite Rdiv_def. reflexivity.
          * assert (~ (S i) < 1). lia. contradiction.
        + assert (0 < 1). lia. exact H2.
        + intro. simpl. rewrite H. unfold Beval. unfold Teval. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0.
          unfold Beval in H0. unfold Teval in H0. symmetry. apply H0.
        + simpl. rewrite Rdiv_def. reflexivity.
Qed.

Theorem uniform_k_inter: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}) (uniform_k k) (fun ps : Pstate => (((1/INR k)*(snd ps y1)) = fst ps (fun st : state => ((fst st) val) = k1))%R).
Proof. intros. apply HConseqLeft with (eta2 := (fun st : Pstate =>
     (((Pteval
          (Pint
             (fun st0 : state =>
              (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0) /\
              (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0))) st) =
       (PTermexp_of_pterm (Pvar y1) st))%R) /\
     ((Pteval
         (Pint
            (fun st0 : state =>
             (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0) /\
             (CBoolexp_of_bexp (Leq (Const k) (Var val)) st0))) st) =
      (Pteval (Pint (fun st0 : state => True)) st)))).
        + simpl. intro. intro. replace (fun st0 : state => ((k <= (fst st0 val))%nat) /\ ((k <= (fst st0 val))%nat)) with (fun st0 : state => ((k <= (fst st0 val))%nat)).
          unfold CTermexp_of_nat in H0. easy. apply functional_extensionality. intro. apply propositional_extensionality. easy.
        + apply HConseqRight with (eta2 := (fun ps : Pstate => (fst ps (fun st : state => ((fst st) val) = k1) <= ((1/INR k)*(snd ps y1)))%R /\ (((1/INR k)*(snd ps y1)) <= fst ps (fun st : state => ((fst st) val) = k1))%R)).
          * intro. lra.
          * apply HAnd.
            - apply HConseqLeft with (eta2:= ({{(prob ((k <= val) /\ (k <= val))) <= y1 /\ (prob ((k <= val) /\ (k <= val))) = (prob true) }})).
              -- intro. intro. split. apply Req_le. easy. easy.
              -- apply uniform_k_UB_inter with (b := (Leq (Const k) (Var val))) (tempA := (CBoolexp_of_bexp (Leq (Const k) (Var val)))).
                  reflexivity. easy. easy.
            - apply HConseqLeft with (eta2:= ({{(prob ((k <= val) /\ (k <= val))) >= y1 /\ (prob ((k <= val) /\ (k <= val))) = (prob true) }})).
               -- intro. intro. split. apply Req_le. easy. easy.
              -- apply uniform_k_LB_inter with (b := (Leq (Const k) (Var val))) (tempA := (CBoolexp_of_bexp (Leq (Const k) (Var val)))).
                  reflexivity. easy. easy.
Qed.

Theorem uniform: forall (k k1 : nat), (k1 < k) -> hoare_triple ({{(prob  (k = val)) = 1 /\ (prob (k = val)) = (prob true)}}) (uniform_k k)  (fun ps : Pstate => (((1/INR k) = fst ps (fun st : state => ((fst st) val) = k1))%R)).
Proof. intros. apply HConseqLeft with (eta2 := {{(prob (k <= val)) = 1 /\ (prob (k <= val)) = (prob true) }}).
        + intro. unfold Pteval. unfold CTermexp_of_Texp. unfold CTermexp_of_nat. unfold Teval. unfold PTerm_of_R. intro.
          assert (fst ps {{true}} = 1%R). transitivity (fst ps (fun st : state => (fst st val) = k)). easy. easy.
          rewrite H1. split. 
          * apply Rle_antisym. 
            - rewrite <- H1. apply measure_inclusion. easy.
            - destruct H0. rewrite <- H0. apply measure_inclusion. intros. Search "eq_le" in Nat. apply eq_le_incl. symmetry. easy. 
          * apply Rle_antisym. 
            - rewrite <- H1. apply measure_inclusion. easy.
            - destruct H0. rewrite <- H0. apply measure_inclusion. intros. Search "eq_le" in Nat. apply eq_le_incl. symmetry. easy.
       + apply HConseq with (eta2 := eta_update_y_p ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }}) y1 (1%R))
                            (eta3 := eta_update_y_p (fun ps : Pstate => (((1/INR k)*(snd ps y1)) = fst ps (fun st : state => ((fst st) val) = k1))%R) y1 (1%R) ).
          * intro. unfold eta_update_y_p. unfold pstate_update. unfold Pteval. simpl. intro.
            split. rewrite t_update_eq. easy. easy.
          * unfold eta_update_y_p. unfold pstate_update. unfold Pteval. simpl. intro. rewrite t_update_eq. lra.
          * apply eliminate_y. easy. easy. apply HConseqLeft with (eta2 := ({{(prob (k <= val)) = y1 /\ (prob (k <= val)) = (prob true) }})).
             - intro. easy.
             - apply uniform_k_inter. apply H.
Qed.

Theorem 
      
