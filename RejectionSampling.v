From PHL Require Import Maps.
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
Require Import Classical.
From PHL Require Import PHLTest.
Import PHL.

Module RejectionSampling.

Definition b0 : string := "b0".
Definition b1 : string := "b1".
Definition y : string := "y".

Definition Rejection_sampling : Cmd := 
<{
  b0 b= true;
  b1 b= true;
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end

}>.


Theorem Rsampling_body : hoare_triple ({{ ((prob (b0 /\ b1)) = 1) /\ (prob (b0 /\ b1)) = (prob true)}})
                            (<{ b0 toss 0.5; b1 toss 0.5 }>)
                            ({{ (prob (b0 /\ b1)) = 0.25 /\ (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }}).
Proof. apply HSeq with (eta2 := ({{(prob b0) = 0.5}})).
          * apply HConseqLeft with (eta2 := btoss_pt b0 0.5 ({{(prob b0) = 0.5}})).
            - intro. unfold btoss_pt. uncoerce_basic. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp.
              unfold Beval. replace (fst ps (fun st : state => CBoolexp_of_bexp (BVar b0) (fst st, b0 !-> True; (snd st)))) with (fst ps (fun st : state => True)). 
              replace (fst ps (fun st : state => CBoolexp_of_bexp (BVar b0) (fst st, b0 !-> False; (snd st)))) with (fst ps (fun st : state => False)).
               rewrite empty_set_measure. intro. destruct H. rewrite <- H0. rewrite H. lra.
              apply equivalence. intro. unfold CBoolexp_of_bexp. unfold Beval. simpl. rewrite t_update_eq. tauto.
              apply equivalence. intro. unfold CBoolexp_of_bexp. unfold Beval. simpl. rewrite t_update_eq. tauto.
            - apply HBToss.
          * apply HAnd.
            + apply HConseqLeft with (eta2 := btoss_pt b1 0.5 ({{ (prob (b0 /\ b1)) = 0.25}})).
              - intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp.
                unfold Beval. unfold Pteval. simpl. intro. uncoerce_basic.
                replace (fst ps (fun st : state => ((b1 !-> True; (snd st)) b0) /\ ((b1 !-> True; (snd st)) b1))) with (fst ps (fun st : state => snd st b0)).
                replace (fst ps (fun st : state => ((b1 !-> False; (snd st)) b0) /\ ((b1 !-> False; (snd st)) b1))) with (fst ps (fun st : state => False)). unfold CBoolexp_of_bexp in H. unfold Beval in H. rewrite H.
                unfold PTerm_of_R. rewrite empty_set_measure. lra. apply equivalence. intro. rewrite t_update_eq. rewrite t_update_neq. tauto.
                easy. apply equivalence. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
              - apply HBToss.
            + apply HConseqRight with (eta2 := ({{ (prob (b0 /\ ~ b1)) = 0.25 }})).
              - uncoerce_basic. intro. replace (fst ps (fun st : state => (~ ((snd st b0) /\ (snd st b1))) /\ ((snd st b0) /\ (~ (snd st b1))))) with (fst ps (fun st : state => (snd st b0) /\ (~ (snd st b1)))).
                easy. apply equivalence. easy.
              - apply HConseqLeft with (eta2 := btoss_pt b1 0.5 ({{ (prob (b0 /\ ~ b1)) = 0.25 }})).
                -- intro. unfold btoss_pt. unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp.
                unfold Beval. unfold Pteval. simpl. intro. uncoerce_basic.
                replace (fst ps (fun st : state => ((b1 !-> True; (snd st)) b0) /\ (~ ((b1 !-> True; (snd st)) b1)))) with (fst ps (fun st : state => False)).
                replace  (fst ps (fun st : state => ((b1 !-> False; (snd st)) b0) /\ (~ ((b1 !-> False; (snd st)) b1)))) with (fst ps (fun st : state => snd st b0 )).
                uncoerce_basic H. unfold CBoolexp_of_bexp in H. unfold Beval in H. rewrite H. rewrite empty_set_measure. lra.
                apply equivalence. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
                apply equivalence. intro. rewrite t_update_eq. rewrite t_update_neq. tauto. easy.
                -- apply HBToss.
Qed.

Theorem Rsampling_loop_y : forall (beta : bexp) (tempA : Assertion), (beta = (And (BVar b0) (BVar b1))) -> (Assertion_equiv tempA (CBoolexp_of_bexp (And (BVar b0) (BVar b1)))) -> 
hoare_triple ({{ ((prob (beta /\ tempA)) <= y) /\ ((prob (beta /\ tempA)) = (prob true)) }})
(<{ 
  while (beta) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) <=  (one_third*y) }}).
Proof. intros. apply HWhileUB with (G := [\{b0 /\ b1\}]) (X := [one_third]) (P := [([0.25%R])]) (T:= [0.25%R]) (i := 0).
        + intro. rewrite H. unfold vector_to_disj. unfold CBoolexp_of_bexp. unfold Beval. tauto.  
        + destruct i. simpl. unfold int_true_eq_one. unfold inner_conj_leq. unfold gamma_leq. unfold gamma_compare. simpl.
          unfold gamma_leq. unfold gamma_compare. unfold apply_func. simpl. intro. uncoerce_basic. unfold CBoolexp_of_bexp. rewrite H. unfold Beval.
          apply HConseqRight with (eta2 := ({{ (prob (b0 /\ b1)) = 0.25 /\ (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }})).
          * intro. uncoerce_basic. lra. 
          * apply Rsampling_body.
          * intro.  assert (~ (S i) < 1). lia. contradiction. 
        + intros. destruct i. 
          * unfold lin_ineq. simpl. unfold one_third. lra.
          * assert (~ (S i) < 1). lia. contradiction.
        + lia.
        + intros. simpl. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0. unfold Beval in H0. symmetry. apply H0.
        + simpl. easy.
Qed.

Theorem Rsampling_loop : hoare_triple ({{ ((prob (b0 /\ b1)) <= y) /\ ((prob (b0 /\ b1)) = (prob true)) }})
(<{ 
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) <=  (one_third*y) }}).
Proof. apply HConseqLeft with (eta2 := ({{ ((prob ((<{ b0 /\ b1 }>) /\ (<{ b0 /\ b1 }>))) <= y) /\ (prob ((<{ b0 /\ b1 }>) /\ (<{ b0 /\ b1 }> ))) = (prob true)}})).
        + intro. uncoerce_basic. replace (fst ps (fun st : state => ((snd st b0) /\ (snd st b1)) /\ ((snd st b0) /\ (snd st b1)))) with ((fst ps (fun st : state => (snd st b0) /\ (snd st b1)))).
          easy. apply equivalence. easy.
        + apply Rsampling_loop_y with (beta := <{b0 /\ b1}>) (tempA := (CBoolexp_of_bexp (And (BVar b0) (BVar b1)))).
          * easy.
          * easy.
Qed.

Theorem RsamplingUB : hoare_triple ({{ ((prob (b0 /\ b1)) = 1) /\ ((prob (b0 /\ b1)) = (prob true)) }})
(<{ 
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) <=  (one_third) }}).

Proof. apply HConseqLeft with (eta2 := ({{ ((prob (b0 /\ b1)) <= 1) /\ ((prob (b0 /\ b1)) = (prob true)) }})). intro. uncoerce_basic. intro. split. lra. tauto. 
        apply HConseq with (eta2 := eta_update_y_p ({{ ((prob (b0 /\ b1)) <= y) /\ ((prob (b0 /\ b1)) = (prob true)) }}) y 1%R) (eta3 := eta_update_y_p ({{ (prob (b0 /\ ~ b1)) <=  (one_third*y) }}) y 1%R).
          + intro. unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. rewrite t_update_eq. easy. 
          + unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. intro. rewrite t_update_eq. rewrite Rmult_1_r. easy.
          + apply eliminate_y.
            * easy.
            * easy.
            * apply HConseqLeft with (eta2 := ({{ ((prob (b0 /\ b1)) <= y) /\ ((prob (b0 /\ b1)) = (prob true)) }})).
              - easy.
              - apply Rsampling_loop.
Qed.

Theorem Rsampling_loop_LB_y : forall (beta : bexp) (tempA : Assertion), (beta = (And (BVar b0) (BVar b1))) -> (Assertion_equiv tempA (CBoolexp_of_bexp (And (BVar b0) (BVar b1)))) -> 
hoare_triple ({{ ((prob (beta /\ tempA)) >= y) /\ ((prob (beta /\ tempA)) = (prob true)) }})
(<{ 
  while (beta) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) >=  (one_third*y) }}).
Proof. intros. apply HWhileLB with (G := [\{b0 /\ b1\}]) (X := [one_third]) (P := [([0.25%R])]) (T:= [0.25%R]) (i := 0).
        + intro. destruct i. simpl. rewrite H. easy. intro. assert (~ (S i) < 1). lia. contradiction.
        + intro. destruct i. intros. assert (~ (j < 0)). lia. contradiction. intros. assert (~ (S i) < 1). lia. contradiction. 
        + intro. destruct i. simpl. intro. left. lra. intro. assert (~ (S i) < 1). lia. contradiction.  
        + destruct i. simpl. unfold int_true_eq_one. unfold inner_conj_geq. unfold gamma_geq. unfold gamma_compare. simpl.
          unfold gamma_geq. unfold gamma_compare. unfold apply_func. simpl. intro. uncoerce_basic. unfold CBoolexp_of_bexp. rewrite H. unfold Beval.
          apply HConseqRight with (eta2 := ({{ (prob (b0 /\ b1)) = 0.25 /\ (prob (~ (b0 /\ b1) /\ (b0 /\ ~ b1))) = 0.25 }})).
          * intro. uncoerce_basic. lra. 
          * apply Rsampling_body.
          * intro.  assert (~ (S i) < 1). lia. contradiction. 
        + intros. destruct i. 
          * unfold lin_ineq_lb. simpl. unfold one_third. lra.
          * assert (~ (S i) < 1). lia. contradiction.
        + lia.
        + intros. simpl. unfold Assertion_equiv in H0. unfold CBoolexp_of_bexp in H0. unfold Beval in H0. symmetry. apply H0.
        + simpl. easy.
Qed.

Theorem Rsampling_loop_LB : hoare_triple ({{ ((prob (b0 /\ b1)) >= y) /\ ((prob (b0 /\ b1)) = (prob true)) }})
(<{ 
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) >=  (one_third*y) }}).
Proof. apply HConseqLeft with (eta2 := ({{ ((prob ((<{ b0 /\ b1 }>) /\ (<{ b0 /\ b1 }>))) >= y) /\ (prob ((<{ b0 /\ b1 }>) /\ (<{ b0 /\ b1 }> ))) = (prob true)}})).
        + intro. uncoerce_basic. replace (fst ps (fun st : state => ((snd st b0) /\ (snd st b1)) /\ ((snd st b0) /\ (snd st b1)))) with ((fst ps (fun st : state => (snd st b0) /\ (snd st b1)))).
          easy. apply equivalence. easy.
        + apply Rsampling_loop_LB_y with (beta := <{b0 /\ b1}>) (tempA := (CBoolexp_of_bexp (And (BVar b0) (BVar b1)))).
          * easy.
          * easy.
Qed.

Theorem RsamplingLB : hoare_triple ({{ ((prob (b0 /\ b1)) = 1) /\ ((prob (b0 /\ b1)) = (prob true)) }})
(<{ 
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) >=  (one_third) }}).

Proof. apply HConseqLeft with (eta2 := ({{ ((prob (b0 /\ b1)) >= 1) /\ ((prob (b0 /\ b1)) = (prob true)) }})). intro. uncoerce_basic. intro. split. lra. tauto. 
        apply HConseq with (eta2 := eta_update_y_p ({{ ((prob (b0 /\ b1)) >= y) /\ ((prob (b0 /\ b1)) = (prob true)) }}) y 1%R) (eta3 := eta_update_y_p ({{ (prob (b0 /\ ~ b1)) >=  (one_third*y) }}) y 1%R).
          + intro. unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. rewrite t_update_eq. easy. 
          + unfold eta_update_y_p. unfold pstate_update. uncoerce_basic. intro. rewrite t_update_eq. rewrite Rmult_1_r. easy.
          + apply eliminate_y.
            * easy.
            * easy.
            * apply HConseqLeft with (eta2 := ({{ ((prob (b0 /\ b1)) >= y) /\ ((prob (b0 /\ b1)) = (prob true)) }})).
              - easy.
              - apply Rsampling_loop_LB.
Qed.

Theorem Rsampling : hoare_triple ({{ ((prob (b0 /\ b1)) = 1) /\ ((prob (b0 /\ b1)) = (prob true)) }})
(<{ 
  while (b0 /\ b1) do 
    b0 toss 0.5; 
    b1 toss 0.5 end
}>) ({{ (prob (b0 /\ ~ b1)) =  (one_third) }}). 
Proof. apply HConseqRight with (eta2 := ({{ (prob (b0 /\ ~ b1)) >=  (one_third) /\ (prob (b0 /\ ~ b1)) <=  (one_third) }})).
        + intro. uncoerce_basic. unfold CBoolexp_of_bexp. unfold Beval. lra.
        + apply HAnd. apply RsamplingLB. apply RsamplingUB.
Qed.    

End RejectionSampling.
