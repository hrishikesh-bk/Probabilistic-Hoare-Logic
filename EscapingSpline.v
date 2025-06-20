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
Import PHL.

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

Theorem asgn2k_1 : forall k : nat, {{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0.5}}
        val := 2*val {{(prob (val = (2*k))) = y1}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val}> {{(prob (val = (2*k))) = y1}}) (TAsgn val <{2*val}>) ({{(prob (val = (2*k))) = y1}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0.5}}) (tasgn_pt val <{2*val}> {{(prob (val = (2*k))) = y1}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl.
                 replace ((fun st : state => (k + (k + 0))%nat = (val !-> (fst st val + (fst st val + 0))%nat; fst st) val)) with ((fun st : state => k = fst st val)).
                 transitivity (0.5%R). apply H. symmetry. apply H.
                  apply functional_extensionality. intros. rewrite t_update_eq. apply propositional_extensionality.
                  split. lia. lia.
              * exact T1.
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k_0 : forall k : nat, {{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0}}
        val := 2*val {{(prob (val = (2*k + 1))) = y1}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val}> {{(prob (val = (2*k + 1))) = y1}}) (TAsgn val <{2*val}>) ({{(prob (val = (2*k + 1))) = y1}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0}}) (tasgn_pt val <{2*val}> {{(prob (val = (2*k + 1))) = y1}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl. assert (fst ps (fun st : state => ~ (k = fst st val)) = 0%R).
                        apply measure_P_eq_true. apply H. replace (snd ps y1) with 0%R. 
                      assert (((fst ps
   (fun st : state =>
    (((k + (k + 0)) + 1)%nat) = ((val !-> ((fst st val) + ((fst st val) + 0))%nat; (fst st)) val))) <= (fst ps (fun st : state => k <> (fst st val))))%R).
            apply measure_inclusion. intro st. replace (((val !-> ((fst st val) + ((fst st val) + 0))%nat; (fst st)) val)) with (((fst st val) + ((fst st val) + 0))%nat).
            lia. symmetry. apply t_update_eq. apply Rle_antisym. apply Rle_trans with (r2:= (fst ps (fun st : state => k <> (fst st val)))).
                  apply H1. right. apply H0. apply Rge_le. apply positive. symmetry. apply H.
              * exact T1. 
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k1_1 : forall k : nat, {{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5}}
        val := 2*val + 1 {{(prob (val = (2*k + 1))) = y2}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k + 1))) = y2}}) (TAsgn val <{2*val + 1}>) ({{(prob (val = (2*k + 1))) = y2}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5}}) (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k + 1))) = y2}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl.
                 replace ((fun st : state => (k + (k + 0) + 1)%nat = (val !-> (fst st val + (fst st val + 0) + 1)%nat; fst st) val)) with ((fun st : state => k = fst st val)).
                 transitivity (0.5%R). apply H. symmetry. apply H.
                  apply functional_extensionality. intros. rewrite t_update_eq. apply propositional_extensionality.
                  split. lia. lia.
              * exact T1.
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem asgn2k1_0 : forall k : nat, {{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0}}
        val := 2*val + 1 {{(prob (val = (2*k))) = y2}}.
Proof. intros.
        assert (T: hoare_triple (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k))) = y2}}) (TAsgn val <{2*val + 1}>) ({{(prob (val = (2*k))) = y2}})). 
          + apply HTAsgn.
          + eapply HConseq.
            ++ assert (T1 : PAImplies ({{ ((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0}}) (tasgn_pt val <{2*val + 1}> {{(prob (val = (2*k))) = y2}})).
              * unfold PAImplies. intros. unfold Pteval. simpl. unfold Pteval in H. simpl in H. unfold CTermexp_of_nat.
                simpl. unfold CTermexp_of_nat in H. Locate "t->". unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term.
                simpl. assert (fst ps (fun st : state => ~ (k = fst st val)) = 0%R).
                        apply measure_P_eq_true. apply H. replace (snd ps y2) with 0%R. 
                      assert (((fst ps
   (fun st : state =>
    ((k + (k + 0))%nat) = ((val !-> (((fst st val) + ((fst st val) + 0)) + 1)%nat; (fst st)) val))) <= (fst ps (fun st : state => k <> (fst st val))))%R).
            apply measure_inclusion. intro st. replace ((val !-> (((fst st val) + ((fst st val) + 0)) + 1)%nat; (fst st)) val) with ((((fst st val) + ((fst st val) + 0)) + 1)%nat).
            lia. symmetry. apply t_update_eq. apply Rle_antisym. apply Rle_trans with (r2:= (fst ps (fun st : state => k <> (fst st val)))).
                  apply H1. right. apply H0. apply Rge_le. apply positive. symmetry. apply H.
              * exact T1. 
            ++ apply PAImpliesItself.
            ++ apply T.
Qed.

Theorem ifthenpre1: forall k: nat, {{(((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5) / (b) \ (((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0) }}
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

Theorem ifthenpre0: forall k: nat, {{(((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0) / (b) \ (((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0.5) }}
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

Theorem intermediate0: forall k : nat, {{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0) /\ y1 = 0.5}}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k)))}}.
Proof. intros. eapply HConseq with (eta2 := {{(((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0) / (b) \ (((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0.5) }}).
        + unfold PAImplies. intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. unfold Pteval.
          simpl. unfold CTermexp_of_nat. unfold PTerm_of_R. intro.
          split. split. split.
          * apply H.
          * replace (fst ps (fun st : state => True /\ snd st b)) with (fst ps (fun st : state => snd st b)).
            - replace (fst ps (fun st : state => snd st b)) with (((fst ps (fun st : state => k = fst st val /\ snd st b)) + (fst ps (fun st : state => ~ (k = fst st val) /\ snd st b)))%R).
              replace ((fst ps (fun st : state => k <> fst st val /\ snd st b))%R) with 0%R. lra.
              assert (0%R = fst ps (fun st : state => k <> fst st val)). symmetry. apply measure_P_eq_true. apply H.
              symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> fst st val)).
              intro. tauto. symmetry. apply H0. transitivity (fst ps (fun st : state => (k = fst st val /\ snd st b) \/ (k <> fst st val /\ snd st b))). 
              apply fin_additivity. intro. tauto. 
              apply equivalence. unfold Assertion_equiv. intro. tauto.
            - apply equivalence. unfold Assertion_equiv. intro. tauto.
          * apply H.
          * split. split. apply H.
            ** replace (fst ps (fun st : state => True /\ ~ snd st b)) with (fst ps (fun st : state => ~ snd st b)).
            - replace (fst ps (fun st : state => ~ snd st b)) with (((fst ps (fun st : state => k = fst st val /\ ~ snd st b)) + (fst ps (fun st : state => ~ (k = fst st val) /\ ~ snd st b)))%R).
              replace ((fst ps (fun st : state => k <> fst st val /\ ~ snd st b))%R) with 0%R. lra.
              assert (0%R = fst ps (fun st : state => k <> fst st val)). symmetry. apply measure_P_eq_true. apply H.
              symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> fst st val)).
              intro. tauto. symmetry. apply H0. transitivity (fst ps (fun st : state => (k = fst st val /\ ~ snd st b) \/ (k <> fst st val /\ ~ snd st b))). 
              apply fin_additivity. intro. tauto. 
              apply equivalence. unfold Assertion_equiv. intro. tauto.
            - apply equivalence. unfold Assertion_equiv. intro. tauto.
          ** apply H.
        + apply PAImpliesItself.
        + apply ifthenpre0.
Qed. 

Theorem intermediate1: forall k : nat, {{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5) /\ y1 = 0}}
<{ if b then val := 2 * val + 1 else val := 2 * val end
}> {{ (y2 + y1) = (prob (val = (2*k + 1)))}}.
Proof. intros. eapply HConseq with (eta2 := {{(((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5) / (b) \ (((prob (val = k)) = 0.5 /\ (prob (val = k)) = (prob true)) /\ y1 = 0) }}).
        + unfold PAImplies. intro. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. unfold Pteval.
          simpl. unfold CTermexp_of_nat. unfold PTerm_of_R. intro.
          split. split. split.
          * apply H.
          * replace (fst ps (fun st : state => True /\ snd st b)) with (fst ps (fun st : state => snd st b)).
            - replace (fst ps (fun st : state => snd st b)) with (((fst ps (fun st : state => k = fst st val /\ snd st b)) + (fst ps (fun st : state => ~ (k = fst st val) /\ snd st b)))%R).
              replace ((fst ps (fun st : state => k <> fst st val /\ snd st b))%R) with 0%R. lra.
              assert (0%R = fst ps (fun st : state => k <> fst st val)). symmetry. apply measure_P_eq_true. apply H.
              symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> fst st val)).
              intro. tauto. symmetry. apply H0. transitivity (fst ps (fun st : state => (k = fst st val /\ snd st b) \/ (k <> fst st val /\ snd st b))). 
              apply fin_additivity. intro. tauto. 
              apply equivalence. unfold Assertion_equiv. intro. tauto.
            - apply equivalence. unfold Assertion_equiv. intro. tauto.
          * apply H.
          * split. split. apply H.
            ** replace (fst ps (fun st : state => True /\ ~ snd st b)) with (fst ps (fun st : state => ~ snd st b)).
            - replace (fst ps (fun st : state => ~ snd st b)) with (((fst ps (fun st : state => k = fst st val /\ ~ snd st b)) + (fst ps (fun st : state => ~ (k = fst st val) /\ ~ snd st b)))%R).
              replace ((fst ps (fun st : state => k <> fst st val /\ ~ snd st b))%R) with 0%R. lra.
              assert (0%R = fst ps (fun st : state => k <> fst st val)). symmetry. apply measure_P_eq_true. apply H.
              symmetry. apply measure_inclusion_0 with (Q := (fun st : state => k <> fst st val)).
              intro. tauto. symmetry. apply H0. transitivity (fst ps (fun st : state => (k = fst st val /\ ~ snd st b) \/ (k <> fst st val /\ ~ snd st b))). 
              apply fin_additivity. intro. tauto. 
              apply equivalence. unfold Assertion_equiv. intro. tauto.
            - apply equivalence. unfold Assertion_equiv. intro. tauto.
          ** apply H.
        + apply PAImpliesItself.
        + apply ifthenpre1.
Qed.

Theorem eliminate_y1_0: forall k : nat, {{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ (y2 + 0.5) = (prob (val = (2*k)))}}.
Proof. intro. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0)}}) y1 0.5%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + y1) = (prob (val = (2*k)))}}) y1 0.5%R).
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.
         intro. split. split. apply H. apply H. rewrite t_update_neq. apply H. easy.
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_neq in H. rewrite t_update_eq in H. apply H. easy.
       + apply eliminate_y.
          * unfold is_analytical_pterm. unfold Pteval. easy.
          * unfold p_inv_y. easy.
          * apply intermediate0.
Qed.

Theorem eliminate_y2_0: forall k : nat, {{(prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{  0.5 = (prob (val = (2*k)))}}.
Proof. intro. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)))}}) y2 0%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + 0.5) = (prob (val = (2*k)))}}) y2 0%R).
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.
         intro. split. apply H. apply H.
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_eq in H. replace (0 + 0.5)%R with 0.5%R in H. apply H. lra.
       + apply eliminate_y.
          * unfold is_analytical_pterm. unfold Pteval. easy.
          * unfold p_inv_y. easy.
          * apply eliminate_y1_0.
Qed.

Theorem eliminate_y1_1: forall k : nat, {{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{ (y2 + 0) = (prob (val = (2*k+1)))}}.
Proof. intro. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)) /\ y2 = 0.5)}}) y1 0%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + y1) = (prob (val = (2*k + 1)))}}) y1 0%R).
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.
         intro. split. split. apply H. apply H. rewrite t_update_neq. apply H. easy.
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_neq in H. rewrite t_update_eq in H. apply H. easy.
       + apply eliminate_y.
          * unfold is_analytical_pterm. unfold Pteval. easy.
          * unfold p_inv_y. easy.
          * apply intermediate1.
Qed.

Theorem eliminate_y2_1: forall k : nat, {{(prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)}}
   <{ if b then val := 2 * val + 1 else val := 2 * val end
}>{{  0.5 = (prob (val = (2*k+1)))}}.
Proof. intro. apply HConseq with (eta2 := eta_update_y_p ({{(((prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)))}}) y2 0.5%R) 
                                 (eta3 := eta_update_y_p ({{ (y2 + 0) = (prob (val = (2*k+1)))}}) y2 0.5%R).
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.
         intro. split. apply H. apply H.
       + unfold PAImplies. intro. unfold eta_update_y_p. unfold Pteval. unfold pstate_update. unfold CTermexp_of_nat. unfold PTermexp_of_pterm.
         unfold PTerm_of_R. unfold CBoolexp_of_bexp. unfold Beval. unfold CTermexp_of_Texp. unfold Pteval. simpl.   
         intro. rewrite t_update_eq in H. replace (0 + 0.5)%R with 0.5%R in H. replace (0.5 + 0)%R with (0.5%R) in H. apply H. lra. lra.
       + apply eliminate_y.
          * unfold is_analytical_pterm. unfold Pteval. easy.
          * unfold p_inv_y. easy.
          * apply eliminate_y1_1.
Qed.

Theorem tossb: forall (k : nat) (r : R), {{ (prob (val = k)) = r /\ (prob (val = k)) = (prob true)}}
b toss 0.5  {{(prob ((val = k)) /\ b) = (0.5*r) /\ (prob ((val = k)) /\ ~ b) = (0.5*r)  /\ (prob (val = k)) = (prob true)}}.
Proof. intro. eapply HConseq with (eta2 := btoss_pt b 0.5 ({{(prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)}})).
        + unfold PAImplies. intro. unfold Pteval. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp.
          unfold assertion_sub_bexp. unfold CBoolexp_of_bexp. unfold CTermexp_of_Texp. unfold CTermexp_of_nat.
          unfold Teval. unfold Beval. unfold PTerm_of_R. replace (1 - 0.5)%R with (0.5)%R. simpl.
          replace ((fun st : state => k = fst st val /\ (b !-> True; snd st) b)) with (fun st : state => k = fst st val). 
          replace ((fun st : state => k = fst st val /\ (b !-> False; snd st) b)) with (fun st : state => False).
          replace ((fun st : state => k = fst st val /\ ~ (b !-> True; snd st) b)) with (fun st : state => False). 
          replace ((fun st : state => k = fst st val /\ ~ (b !-> False; snd st) b)) with (fun st : state => k = fst st val).  
          * intros. split. 
            - rewrite empty_set_measure. lra.
            - split. 
              -- rewrite empty_set_measure. lra.
              -- lra. 
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * apply functional_extensionality. intro. rewrite t_update_eq. apply propositional_extensionality. tauto.
          * lra.
        + apply PAImpliesItself.
        + apply HBToss.
Qed.

Theorem body1: forall (k : nat) (r : R), {{ (prob (val = k)) = r /\ (prob (val = k)) = (prob true)}}
body {{  0.5*r = (prob (val = (2*k+1)))}}.
Proof. intro. eapply HSeq with (eta2:= {{(prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)}}).
        + apply tossb.
        + apply eliminate_y2_1.
Qed.

Theorem body2: forall (k : nat) (r : R), {{ (prob (val = k)) = r /\ (prob (val = k)) = (prob true)}}
body {{  0.5*r = (prob (val = (2*k)))}}.
Proof. intro. eapply HSeq with (eta2:= {{(prob ((val = k)) /\ b) = 0.5 /\ (prob ((val = k)) /\ ~ b) = 0.5  /\ (prob (val = k)) = (prob true)}}).
        + apply tossb.
        + apply eliminate_y2_0.
Qed. 

Theorem ifthen_intermediate : forall k : nat, 

Theorem body1: forall k : nat, {{(prob (val = k)) = 1 /\ (prob (val = k)) = (prob true)}} body 
                                {{(prob (val = (2 * k))) = 0.5}}.
Proof.
Admitted.

Theorem body2: forall k : nat, {{(prob (val = k)) = 1 /\ (prob (val = k)) = (prob true)}} body 
                                {{(prob (val = (2*k + 1))) = 0.5}}.
Proof.
Admitted.
