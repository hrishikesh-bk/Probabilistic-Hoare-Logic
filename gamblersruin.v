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


Definition b:string := "b". 


Definition GamblersRuin_Body (x0: string) : Cmd :=
<{
if (x0 >= 1) 
then (b toss ((1/3)%R);
      (if b then (x0 := x0 + 1) else (x0 := x0 - 1) end))
else skip
end
}>.

(* Want to prove ->  From x -> 2/3 chance of x-1 and 1/3 chace of x+` *)
Check \{ (x<=1)\}.


(*  Gamblers Ruin Helper theorems     *)

Theorem xlt1_Else: ( forall x0 y1 : string,  hoare_triple ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }}) <{skip}> ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }}) ).
Proof.
  - intros. apply HSkip.
Qed.


Theorem xlt1_If: ( forall x0 y2 : string,  hoare_triple ({{((prob true) = 0) /\ (y2 = 0) }}) <{(b toss ((1/3)%R); (if b then (x0 := x0 + 1) else (x0 := x0 - 1) end))}> 
      ({{ (0 = (prob ~(x0 >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }}) ).
Proof.
intros. apply AddRigidRight.
 eapply HConseq with (eta1 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta2 := ({{((prob true) = 0) /\ (y2 = 0) }}))
                             (eta3 := ({{((prob true) = 0) /\ (y2 = 0) }})).
 - easy. 
 - unfold PAImplies. intros. destruct H. uncoerce_basic. split. uncoerce_basic H. uncoerce_basic H0. symmetry. apply empty_measure_inclusion2 with (mu := fst ps) (P := (fun st : state => ~ 1 <= fst st x0)).
   easy. easy.
  - uncoerce_basic.
 set (eta := (fun st : Pstate => ((Pteval (Pint {{true}}) st) = (PTerm_of_R 0 st)) /\ ((PTermexp_of_pterm (Pvar y2) st) = (PTerm_of_R 0 st)))). simpl in eta. unfold PTerm_of_R in eta.
   eapply HSeq with (eta1 := eta) (eta2 := eta) (eta3 := eta).
  -- eapply HConseq with (eta1 := eta) (eta3 := eta) (eta4 := eta) (eta2:= (btoss_pt b (1/3)%R eta)).
    2: easy. 2: apply HBToss.
    unfold PAImplies. intros. unfold eta. simpl. unfold btoss_pt. simpl. unfold PTerm_of_R. split.
    --- unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. rewrite <- Rmult_plus_distr_r.
        replace ((1 / 3) + (1 - 1 / 3))%R with 1%R by field. rewrite Rmult_1_l. apply H.
    --- apply H.
 -- eapply HConseq with (eta1:= eta) (eta2:= (psfBpsf eta eta b)) (eta3 := ({{(y2 + y2 = (prob true)) /\ (y2 = 0)}})).
  --- unfold PAImplies. intros. unfold psfBpsf. split. unfold PAcondB. unfold Measure_cond_B. simpl.
      unfold eta. simpl. split. unfold PTerm_of_R. ---- unfold eta in H. destruct H. pose proof empty_measure_inclusion (fst ps).
      unfold assert_of_Prop in H1. pose proof H1 H. specialize (H2 (fun st => True /\ (snd st b))). apply H2. 
---- unfold eta in H. apply H.
---- unfold PAcondB. unfold Measure_cond_B. simpl. unfold eta. simpl. split.
      ----- unfold eta in H. destruct H. pose proof empty_measure_inclusion (fst ps). unfold assert_of_Prop in H1. pose proof H1 H. specialize (H2 (fun st : state => True /\ (~ (snd st b)))). apply H2.
      ----- unfold eta in H. destruct H. apply H0.
--- simpl. unfold eta. unfold PTerm_of_R. unfold PAImplies. intros. split. destruct H. rewrite -> H0 in H. rewrite Rplus_0_l in H. symmetry. apply H. simpl. unfold eta. unfold PTerm_of_R. unfold PAImplies. intros. easy.
--- eapply HAnd. ----- apply HIfThen. 
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x0 (<{x0 + 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
                  easy. unfold eta. unfold PAImplies. intros. destruct H. rewrite -> H. assumption. apply HTAsgn.
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x0 (<{x0  - 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
                  easy. unfold eta. unfold PAImplies. intros. destruct H. rewrite -> H. assumption. apply HTAsgn.
      ----- unfold eta. unfold psfBpsf. unfold PAcondB. simpl. unfold Measure_cond_B. simpl. eapply HConseq with (eta2 := (fun ps : Pstate => ((snd ps y2) = (0%R)))) 
(eta1 := (fun ps : Pstate =>
   (((fst ps (fun st : state => True /\ (snd st b))) = (0%R)) /\
    ((snd ps y2) = (0%R))) /\
   (((fst ps (fun st : state => True /\ (~ (snd st b)))) =
     (0%R)) /\ ((snd ps y2) = (0%R))))) (eta3 := (fun st : Pstate => (snd st y2) = (PTerm_of_R 0 st))) (eta4 := (fun st : Pstate => (snd st y2) = (PTerm_of_R 0 st))). 
    ------ unfold PAImplies. intros. simpl. destruct H. destruct H0. apply H1.
    ------ unfold PAImplies. intros. easy.
    ------ unfold PTerm_of_R. apply RigidUnchanged.
Qed.
Definition y1: string := "y1".
Definition y2: string := "y2".


Theorem xlt1: forall x0: string,  hoare_triple ({{ ((prob ~(x0 >= 1)) = 1) /\ ((prob ~(x0 >= 1)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ (prob ~(x0 >= 1)) = 1  /\ ((prob (true)) = 1)}}).
Proof.
intros.
uncoerce_basic.
eapply HElimv with (y := y1) (p :=  (Preal 1%R)) (eta1 := ({{ ((prob ~(x0 >= 1)) = 1) /\ ((prob ~(x0 >= 1)) = (prob true)) }})).
 - uncoerce_basic.
   eapply HElimv with (y := y2) (p :=  (Preal 0%R)) (eta1 := ({{(((prob ~(x0 >= 1)) = 1) /\ ((prob ~(x0 >= 1)) = (prob true)) ) /\ (y1 = 1) }})).
    -- uncoerce_basic. Check  <{ x0 >= 1 }>.
       eapply HConseq with (eta2 := (psfBpsf ({{((prob true) = 0) /\ (y2 = 0) }}) ({{((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true)) /\ (y1 = 1) }}) (<{ x0 >= 1 }>))) 
                    (eta3 :=  ({{ (y2 + y1 = (prob ~(x0 >=1)) /\ y1 = 1 /\ y2 = 0) /\ (y2 + y1 = (prob true) /\ y1 = 1 /\ y2 = 0)  }})).
        --- uncoerce_basic. unfold PAImplies. intros. unfold psfBpsf. split. unfold PAcondB. simpl. split. unfold Measure_cond_B. simpl. 
            replace (fun st : state => True /\ 1 <= fst st x0) with (fun st : state => 1 <= fst st x0).
            pose proof measure_true_dest (fst ps) (fun st : state => 1 <= fst st x0).
            destruct H. destruct H. destruct H. rewrite -> H in H3. rewrite <- H3 in H0. rewrite H in H0. lra.
            apply functional_extensionality. intros. apply propositional_extensionality. easy.
            easy.
           unfold PAcondB. simpl. split. unfold Measure_cond_B. simpl. replace (fun st : state => ~ 1 <= fst st x0 /\ ~ 1 <= fst st x0) with (fun st : state => ~ 1 <= fst st x0).
           easy. apply functional_extensionality. intros. apply propositional_extensionality. split. intros. split. easy. easy.
           easy. unfold Measure_cond_B. simpl. split. apply equivalence. easy. easy.
    --- uncoerce_basic. unfold PAImplies. intros. destruct H. destruct H0. destruct H1. rewrite H1 in H0. rewrite H2 in H0. replace 1%R with (0 + 1)%R. rewrite H1 in H. rewrite H2 in H.  easy. lra.
    --- uncoerce_basic. apply HAnd.
        apply HAnd.
        apply HIfThen.
       ---- apply HConseqRight with (eta2 := ({{ (0 = (prob ~(x0 >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }})).
            unfold PAImplies. intros. simpl in H. destruct H. destruct H. rewrite H0. easy.
            apply xlt1_If.
       ---- apply HConseq with (eta2 := ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }}))
                               (eta3 := ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }})).
             easy.
            unfold PAImplies. intros. simpl in H. destruct H. destruct H. rewrite H0. easy.
            simpl. apply xlt1_Else.
       ---- apply HAnd.
        ----- apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y1 = 1%R)). unfold PAImplies. unfold psfBpsf. unfold PAcondB.
              simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. intros. rewrite <- H. easy. intros. rewrite H. easy.
        ----- apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y2 = 0%R)). unfold PAImplies. unfold psfBpsf. unfold PAcondB.
              simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. intros. rewrite <- H. easy. intros. rewrite H. easy.
       ---- apply HAnd. apply HIfThen. apply HConseq with (eta2 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta3 := ({{ (0 = (prob ~(x0 >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }})).
             easy. simpl. unfold PAImplies. intros. destruct H. destruct H. rewrite H0. easy. simpl. apply xlt1_If.
             apply HConseq with (eta2 := ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }})) (eta3 := ({{(((prob  ~(x0>=1)) = 1) /\ ((prob  ~(x0>=1)) = (prob true))) /\ (y1 = 1) }})).
             easy. unfold PAImplies. intros. simpl in H. destruct H. destruct H. rewrite H0. rewrite <- H1. easy. apply xlt1_Else.
             apply HAnd. apply HConseqLeft with (eta2 := ({{y1 = 1}})). unfold PAImplies. unfold psfBpsf. simpl. unfold PAcondB.
             simpl. intros. easy. apply HFree. unfold is_analytical. intros.  split. rewrite H. easy. rewrite H. easy. 
             apply HConseqLeft with (eta2 := ({{y2 = 0}})). unfold PAImplies. unfold psfBpsf. simpl. unfold PAcondB.
             simpl. intros. easy. apply HFree. unfold is_analytical. intros.  split. rewrite H. easy. rewrite H. easy.
-- easy. -- easy. - easy. - easy.
Qed.

Definition half: R := (1/2)%R.
Definition twothird: R := (2/3)%R.
Definition onethird: R := (1/3)%R.
Definition y3: string := "y3".
Definition y4: string := "y4".


(* chain the above two usinf HIfThen and get the actual rule to be used in the while proof *)
Theorem xgeq1:forall (x0: string) (n: nat), (n >= 1) ->  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})
              .
Proof.
intros. uncoerce_basic.
assert (\{ (x0 = n) /\ (1 <= x0) \} = \{ (x0 = n) \}) as G. uncoerce_basic. apply functional_extensionality. intros. unfold CTermexp_of_nat. unfold CTermexp_of_Texp. simpl. apply propositional_extensionality.
split. easy. split. easy. rewrite <- H0. easy. uncoerce_basic G. set (ifcase := ({{ (((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true))) /\ (y1 = twothird) /\ (y2 = 0) /\ (y3 = onethird) }})). uncoerce_basic ifcase.
set (elsecase := ({{((prob true) = 0) /\ (y2 = 0) }})).  uncoerce_basic elsecase.
assert ((eta_update_y_p ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) y1 twothird) = ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }})) as Hlpr. uncoerce_basic.
 - unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy.
   
- replace (fun st : Pstate =>
   fst st (fun st0 : state => n - 1 = fst st0 x0) =
   twothird /\
   fst st
     (fun st0 : state => (n + 1)%nat = fst st0 x0) =
   onethird /\ fst st {{true}} = 1%R) with 

       (fun st : Pstate =>
   (fst st (fun st0 : state => n - 1 = fst st0 x0) =
   twothird /\
   fst st
     (fun st0 : state => (n + 1)%nat = fst st0 x0) =
   onethird) /\ fst st {{true}} = 1%R).
uncoerce_basic Hlpr. rewrite <- Hlpr. apply HElimv.
  -- (* Main proof. *)
     assert ((eta_update_y_p ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) }}) y2 (0%R)) = ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) }})) as Hlpr2. uncoerce_basic. 
     unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy. uncoerce_basic Hlpr2. uncoerce_basic.
     eapply HConseqLeft with (eta2 := (eta_update_y_p
          (fun st : Pstate =>
           fst st (fun st0 : state => n = fst st0 x0) = 1%R /\
           fst st (fun st0 : state => n = fst st0 x0) = fst st {{true}} /\
           snd st y1 = twothird) y2 (Preal 0))). rewrite <- Hlpr2. easy.
    apply HElimv. uncoerce_basic.
       assert ((eta_update_y_p ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) /\ (y2 = 0)}}) y3 onethird) = ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) /\ (y2 = 0) }})) as Hlpr3. uncoerce_basic. 
     unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy. uncoerce_basic Hlpr3. uncoerce_basic.
     eapply HConseqLeft with (eta2 := (eta_update_y_p
           (fun st : Pstate =>
            ((fst st (fun st0 : state => n = (fst st0 x0))) =
             (1%R)) /\
            (((fst st (fun st0 : state => n = (fst st0 x0))) =
              (fst st {{true}})) /\
             (((snd st y1) = twothird) /\ ((snd st y2) = (0%R)))))
           y3 (Preal onethird))). rewrite <- Hlpr3. easy.
    apply HElimv. uncoerce_basic.
    apply HAnd.
       eapply HConseqLeft with (eta2 :=  (psfBpsf ifcase elsecase (<{x0 >= 1}>))).
  --- simpl. unfold PAImplies. intros. uncoerce_basic H0. unfold psfBpsf. split. split. unfold Measure_cond_B. simpl. split. rewrite -> G. easy.
   rewrite G. destruct H0. destruct H0. rewrite H0. 
   pose proof  measure_inclusion_true (fst ps) (fun st : state => True /\ 1 <= fst st x0). unfold assert_of_Prop in H3. destruct H2. rewrite <- H2 in H3. rewrite -> H0 in H3.
   pose proof measure_inclusion (fst ps) (fun st : state => n = fst st x0)  (fun st : state => True /\ 1 <= fst st x0).
   assert (forall st : state, (fun st0 : state => n = fst st0 x0) st -> (fun st0 : state => True /\ 1 <= fst st0 x0) st).
   intros. split. easy. rewrite <- H6. easy. pose proof H5 H6. rewrite H0 in H7. apply Rle_antisym. easy. easy.
   ---- destruct H0. destruct H0. simpl. easy.
 ---- unfold PAcondB. unfold elsecase. simpl. unfold Measure_cond_B. simpl. split.
        -----
               assert (fst ps (fun st0 : state => n = fst st0 x0) = (fst ps  (fun st : state => 1 <= fst st x0))). apply Rle_antisym.
                     apply measure_inclusion. intros. rewrite <- H1. easy. destruct H0. destruct H0. destruct H2. rewrite H2. apply measure_inclusion_true.
                     assert ((fst ps (fun st : state => True /\ ~ 1 <= fst st x0)) = (fst ps (fun st : state => ~ 1 <= fst st x0))).
                      apply equivalence with (mu := fst ps) (P := (fun st : state => True /\ ~ 1 <= fst st x0)) (Q := (fun st : state => ~ 1 <= fst st x0)).
                      unfold Assertion_equiv. intros. easy. rewrite H2.
                      assert ( (fst ps {{true}} = ((fst ps) (\{ x0 >= 1\})) + ((fst ps) (\{ ~ (x0 >= 1) \})))%R).
                        ------ apply measure_true_dest with (mu := fst ps) (Q := (\{ x0 >= 1\})).
            ------ destruct H0. destruct H0. destruct H5. rewrite H5 in H0. rewrite H0 in H3. uncoerce_basic H3. rewrite <- H1 in H3. rewrite H5 in H3. rewrite H0 in H3. lra.
        ----- easy.
 --- (* If Then Else stuff - split into 3 cases. one for consluding n-1, n+1, and finally total measure *)
      apply HAnd.
      (* n -1 case.*) 
      eapply HConseqRight with (eta2 :=  ({{ y1 + y2 = (prob (x0 = (n - 1))) /\ y1 = twothird /\ y2 = 0}})).
        ---- uncoerce_basic. unfold PAImplies. intros. destruct H0. destruct H1. 
             rewrite -> H1 in H0. rewrite -> H2 in H0. unfold twothird in H0. unfold twothird. assert ((2 / 3 + 0)%R = (2/3)%R).
              ring. rewrite  <- H3. easy.
        ---- uncoerce_basic. apply HAnd.
                ----- apply HIfThen.
------ eapply HSeq with (eta2 := ({{ ifcase /\((prob b) = onethird) /\ ( (prob (~b)) = twothird)}})). unfold twothird. unfold onethird.
        ------- uncoerce_basic. unfold CBoolexp_of_bexp.
                eapply HConseqLeft with (eta2 := (btoss_pt b (1 / 3)%R  (fun st : Pstate => ifcase st /\
                                   fst st (fun st0 : state => Beval (BVar b) st0) = (1 / 3)%R /\
                                   fst st (fun st0 : state => ~ snd st0 b) = (2 / 3)%R))).
                unfold PAImplies. unfold ifcase. intros. unfold btoss_pt. simpl. 
                unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
                destruct H0. destruct H0. rewrite -> H0. rewrite -> H0 in H2. rewrite <- H2. split.
                lra. unfold t_update. simpl. rewrite <- H2. pose proof measure_false_is_zero (fst ps).
                rewrite -> H3. split. lra.
                  assert ((fun _ : state => ~ True) = ({{false}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H4. rewrite H3.
                  assert ((fun _ : state => ~ False) = ({{true}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H5. rewrite <- H2. lra.
        apply HBToss.
------- uncoerce_basic. unfold ifcase.
        apply HConseqRight with (eta2 :=  ({{ y2 + y1 = (prob (x0 = (n - 1))) /\ y1 = twothird /\ y2 = 0}})). unfold PAImplies. uncoerce_basic. intros.
        destruct H0. destruct H1. 
             rewrite -> H2 in H0. lra.
         uncoerce_basic. apply HAnd.
        apply HConseqLeft with (eta2 := (psfBpsf ({{ (((prob (x0 = n)) = (prob true))) /\ (y2 = 0) /\ (prob b) = onethird}})  ({{ (((prob (x0 = n)) = (prob true))) /\ ((prob (x0 = n)) = twothird)  /\ (y1 = twothird) /\ (prob (~b)) = twothird}}) (<{b}>))).
      uncoerce_basic. unfold PAImplies. unfold psfBpsf. unfold ifcase. split. split. unfold Measure_cond_B. simpl. 
       replace (fun st : state => True /\ snd st b) with (fun st : state => snd st b). apply Rle_antisym.
       apply measure_inclusion. easy. replace (fun st : state => snd st b) with (fun st : state =>  (n = fst st x0 /\ snd st b)
                                                                                                    \/ (~(n = fst st x0) /\ snd st b)).
       replace (fst ps (fun st : state =>  (n = fst st x0 /\ snd st b) \/ (~(n = fst st x0) /\ snd st b))) 
            with (((fst ps (fun st : state =>  ((n = fst st x0) /\ snd st b))) + 
                 (fst ps (fun st : state =>  (~(n = fst st x0) /\ snd st b))))%R).
     replace (fst ps (fun st : state => n <> fst st x0 /\ snd st b)) with 0%R. lra.
     apply Rle_antisym. pose proof positive (fst ps) (fun st : state => n <> fst st x0 /\ snd st b) as Bd. lra.
     replace 0%R with (fst ps (fun st : state => n <> fst st x0)). apply measure_inclusion. easy.
    apply measure_P_eq_true. easy. apply fin_additivity. easy. apply functional_extensionality. intros. apply propositional_extensionality.
    split. intros. destruct H1. easy. easy. intros. destruct (Nat.eq_dec n (fst x1 x0)) as [Heq | Hneq]. left. easy. right. easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy. simpl. split. easy.
    unfold Measure_cond_B. uncoerce_basic. replace (fun st : state => snd st b /\ snd st b) with (fun st : state => snd st b). easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy.
    unfold PAcondB. unfold Measure_cond_B. simpl.
    replace (fun st : state => True /\ ~ snd st b) with (fun st : state => ~ snd st b). split. apply Rle_antisym.
       apply measure_inclusion. easy. replace (fun st : state => ~ snd st b) with (fun st : state =>  (n = fst st x0 /\ ~ snd st b)
                                                                                                    \/ (~(n = fst st x0) /\ ~ snd st b)).
       replace (fst ps (fun st : state =>  (n = fst st x0 /\ ~ snd st b) \/ (~(n = fst st x0) /\ ~ snd st b))) 
            with (((fst ps (fun st : state =>  ((n = fst st x0) /\ ~ snd st b))) + 
                 (fst ps (fun st : state =>  (~(n = fst st x0) /\ ~ snd st b))))%R).
     replace (fst ps (fun st : state => n <> fst st x0 /\ ~ snd st b)) with 0%R. lra.
     apply Rle_antisym. pose proof positive (fst ps) (fun st : state => n <> fst st x0 /\ ~ snd st b) as Bd. lra.
     replace 0%R with (fst ps (fun st : state => n <> fst st x0)). apply measure_inclusion. easy.
    apply measure_P_eq_true. easy. apply fin_additivity. easy. apply functional_extensionality. intros. apply propositional_extensionality.
    split. intros. destruct H1. easy. easy. intros. destruct (Nat.eq_dec n (fst x1 x0)) as [Heq | Hneq]. left. easy. right. easy.
    replace (fun st : state => ~ snd st b /\ ~ snd st b) with (fun st : state =>  ~ snd st b). split. apply Rle_antisym.
    destruct H0. destruct H1. rewrite <- H2. apply measure_inclusion. easy.
    destruct H0. destruct H1. destruct H0. destruct H0.
            pose proof (AddTrue (fst ps) (fun st : state => n = (fst st x0)) (fun st : state => (~ (snd st b)))
                        ) H4 as H5. rewrite <- H5. rewrite H2. lra.
                                          easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy. 
    apply functional_extensionality. intros. apply propositional_extensionality. easy.
 -------- uncoerce_basic. apply HIfThen. 
         apply HConseqRight with (eta2 := ({{ 0 = (prob (x0 = (n - 1))) /\ y2 = 0 }})).
          unfold PAImplies. uncoerce_basic. intros. lra. apply HAnd.
          --------- uncoerce_basic. apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 + 1}>)  ({{0 = (prob (x0 = (n - 1)))}}))).
                    unfold PAImplies. uncoerce_basic. intros. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl.
                    unfold t_update. simpl. rewrite String.eqb_refl. simpl. destruct H0.
                    pose proof (measure_P_eq_true (fst ps) ((fun st : state => n = fst st x0))) H0. simpl in H2. symmetry.
                    apply measure_inclusion_0 with (mu := fst ps) (P := (fun st : state => n - 1 = (fst st x0 + 1)%nat))
                          (Q := (fun st : state => n <> fst st x0) ). lia. easy. apply HTAsgn.
            --------- apply HConseqLeft with (eta2 := ({{ y2 = 0 }})). easy.
          apply RigidUnchanged.      
     --------- apply HConseqRight with (eta2 := ({{ twothird = (prob (x0 = (n - 1))) /\ y1 = twothird }})).
               unfold PAImplies. uncoerce_basic. intros. lra. apply HAnd.
          ---------- uncoerce_basic. apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 - 1}>)  ({{twothird = (prob (x0 = (n - 1)))}}))).
                    unfold PAImplies. uncoerce_basic. intros. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl.
                    unfold t_update. simpl. rewrite String.eqb_refl. simpl. destruct H0. simpl. 
                   (* n = x to n-1 = x0 -1 *)
                    replace (fst ps (fun st : state => n - 1 = fst st x0 - 1)) with (fst ps (\{ (x0 = n)  /\ ((x0 - 1) = (n - 1)) \})).
                    replace (\{ (x0 = n)  /\ ((x0 - 1) = (n - 1)) \}) with (\{ (x0 = n) \}). easy. apply functional_extensionality.
                    intros. apply propositional_extensionality. split. lia. lia. symmetry. 
                    apply AddTrue with (mu := fst ps) (P := (\{ (x0 = n) \})) (Q := (\{ (x0 - 1) = (n - 1) \})) . easy.
                    apply HTAsgn.
            ---------- apply HConseqLeft with (eta2 := ({{ y1 = twothird }})). easy.
          apply RigidUnchanged.   
-------- apply HAnd. apply HConseqLeft with (eta2 := (fun st : Pstate => (snd st y1) = twothird)). easy. apply RigidUnchanged.
         apply HConseqLeft with (eta2 := (fun st : Pstate => (snd st y2) = 0%R)). easy. apply RigidUnchanged.
------ unfold elsecase. apply HConseqRight with (eta2 :=  (fun st : Pstate =>
   and (eq (fst st (fun _ : state => True)) 0%R)
     (eq (snd st y2) 0%R))). 2: apply HSkip. unfold PAImplies. intros. destruct H0. rewrite H1.
     pose proof empty_measure_inclusion (fst ps). pose proof H2 H0. specialize H3 with (fun st : state => n - 1 = fst st x0). easy.
----- apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y1 = twothird /\ snd st y2 = 0%R)). unfold PAImplies.
       unfold psfBpsf. unfold PAcondB. unfold ifcase. unfold elsecase.  simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. rewrite H0. easy.
       rewrite H0. easy.
---- (* n + 1 case *)
      eapply HConseqRight with (eta2 :=  ({{ y3 + y2 = (prob (x0 = (n + 1))) /\ y3 = onethird /\ y2 = 0}})).
        ----- uncoerce_basic. unfold PAImplies. intros. destruct H0. destruct H1. 
             rewrite -> H1 in H0. rewrite -> H2 in H0. unfold onethird in H0. unfold onethird. assert ((1 / 3 + 0)%R = (1/3)%R).
              ring. rewrite  <- H3. easy.
        ----- uncoerce_basic. apply HAnd.
                ------ apply HIfThen.
------- eapply HSeq with (eta2 := ({{ ifcase /\((prob b) = onethird) /\ ( (prob (~b)) = twothird)}})). unfold twothird. unfold onethird.
        -------- uncoerce_basic. unfold CBoolexp_of_bexp.
                eapply HConseqLeft with (eta2 := (btoss_pt b (1 / 3)%R  (fun st : Pstate => ifcase st /\
                                   fst st (fun st0 : state => Beval (BVar b) st0) = (1 / 3)%R /\
                                   fst st (fun st0 : state => ~ snd st0 b) = (2 / 3)%R))).
                unfold PAImplies. unfold ifcase. intros. unfold btoss_pt. simpl. 
                unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
                destruct H0. destruct H0. rewrite -> H0. rewrite -> H0 in H2. rewrite <- H2. split.
                lra. unfold t_update. simpl. rewrite <- H2. pose proof measure_false_is_zero (fst ps).
                rewrite -> H3. split. lra.
                  assert ((fun _ : state => ~ True) = ({{false}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H4. rewrite H3.
                  assert ((fun _ : state => ~ False) = ({{true}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H5. rewrite <- H2. lra.
        apply HBToss.
-------- uncoerce_basic. unfold ifcase.
        apply HConseqRight with (eta2 :=  ({{ y3 + y2 = (prob (x0 = (n + 1))) /\ y3 = onethird /\ y2 = 0}})). unfold PAImplies. uncoerce_basic. intros.
        destruct H0. destruct H1. 
             rewrite -> H2 in H0. lra.
         uncoerce_basic. apply HAnd.
        apply HConseqLeft with (eta2 := (psfBpsf ({{ (((prob (x0 = n)) = (prob true))) /\ ((prob (x0 = n)) = onethird) /\ (y3 = onethird) /\ (prob b) = onethird}})  ({{ (((prob (x0 = n)) = (prob true))) /\ ((prob (x0 = n)) = twothird)  /\ (y2 = 0) /\ (prob (~b)) = twothird}}) (<{b}>))).
       uncoerce_basic. unfold PAImplies. unfold psfBpsf. unfold ifcase. split. split. unfold Measure_cond_B. simpl. 
       replace (fun st : state => True /\ snd st b) with (fun st : state => snd st b). apply Rle_antisym.
       apply measure_inclusion. easy. replace (fun st : state => snd st b) with (fun st : state =>  (n = fst st x0 /\ snd st b)
                                                                                                    \/ (~(n = fst st x0) /\ snd st b)).
       replace (fst ps (fun st : state =>  (n = fst st x0 /\ snd st b) \/ (~(n = fst st x0) /\ snd st b))) 
            with (((fst ps (fun st : state =>  ((n = fst st x0) /\ snd st b))) + 
                 (fst ps (fun st : state =>  (~(n = fst st x0) /\ snd st b))))%R).
     replace (fst ps (fun st : state => n <> fst st x0 /\ snd st b)) with 0%R. lra.
     apply Rle_antisym. pose proof positive (fst ps) (fun st : state => n <> fst st x0 /\ snd st b) as Bd. lra.
     replace 0%R with (fst ps (fun st : state => n <> fst st x0)). apply measure_inclusion. easy.
    apply measure_P_eq_true. easy. apply fin_additivity. easy. apply functional_extensionality. intros. apply propositional_extensionality.
    split. intros. destruct H1. easy. easy. intros. destruct (Nat.eq_dec n (fst x1 x0)) as [Heq | Hneq]. left. easy. right. easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy. simpl. split. unfold Measure_cond_B. 
    destruct H0. replace (fst ps (fun st : state => n = fst st x0 /\ Beval b st)) with (fst ps (fun st : state =>  Beval b st)).
    easy. apply AddTrue. easy.
    unfold Measure_cond_B. uncoerce_basic. replace (fun st : state => snd st b /\ snd st b) with (fun st : state => snd st b). easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy.
    unfold PAcondB. unfold Measure_cond_B. simpl.
    replace (fun st : state => True /\ ~ snd st b) with (fun st : state => ~ snd st b). split. apply Rle_antisym.
       apply measure_inclusion. easy. replace (fun st : state => ~ snd st b) with (fun st : state =>  (n = fst st x0 /\ ~ snd st b)
                                                                                                    \/ (~(n = fst st x0) /\ ~ snd st b)).
       replace (fst ps (fun st : state =>  (n = fst st x0 /\ ~ snd st b) \/ (~(n = fst st x0) /\ ~ snd st b))) 
            with (((fst ps (fun st : state =>  ((n = fst st x0) /\ ~ snd st b))) + 
                 (fst ps (fun st : state =>  (~(n = fst st x0) /\ ~ snd st b))))%R).
     replace (fst ps (fun st : state => n <> fst st x0 /\ ~ snd st b)) with 0%R. lra.
     apply Rle_antisym. pose proof positive (fst ps) (fun st : state => n <> fst st x0 /\ ~ snd st b) as Bd. lra.
     replace 0%R with (fst ps (fun st : state => n <> fst st x0)). apply measure_inclusion. easy.
    apply measure_P_eq_true. easy. apply fin_additivity. easy. apply functional_extensionality. intros. apply propositional_extensionality.
    split. intros. destruct H1. easy. easy. intros. destruct (Nat.eq_dec n (fst x1 x0)) as [Heq | Hneq]. left. easy. right. easy.
    replace (fun st : state => ~ snd st b /\ ~ snd st b) with (fun st : state =>  ~ snd st b). split. apply Rle_antisym.
    destruct H0. destruct H1. rewrite <- H2. apply measure_inclusion. easy.
    destruct H0. destruct H1. destruct H0. destruct H0.
            pose proof (AddTrue (fst ps) (fun st : state => n = (fst st x0)) (fun st : state => (~ (snd st b)))
                        ) H4 as H5. rewrite <- H5. rewrite H2. lra.
                                          easy.
    apply functional_extensionality. intros. apply propositional_extensionality. easy. 
    apply functional_extensionality. intros. apply propositional_extensionality. easy.
 --------- uncoerce_basic. apply HIfThen. 
     ---------- apply HConseqRight with (eta2 := ({{ onethird = (prob (x0 = (n + 1))) /\ y3 = onethird }})).
               unfold PAImplies. uncoerce_basic. intros. lra. apply HAnd.
          ----------- uncoerce_basic. apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 + 1}>)  ({{onethird = (prob (x0 = (n + 1)))}}))).
                    unfold PAImplies. uncoerce_basic. intros. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl.
                    unfold t_update. simpl. rewrite String.eqb_refl. simpl. destruct H0. simpl. 
                    (* n = x to n+1 = x0+1 *)
                    replace (fst ps (fun st : state => ((n + 1) = (fst st x0) + 1)%nat)) with (fst ps (\{ (x0 = n)  /\ ((x0 + 1) = (n + 1)) \})).
                    replace (\{ (x0 = n)  /\ ((x0 + 1) = (n + 1)) \}) with (\{ (x0 = n) \}). easy. apply functional_extensionality.
                    intros. apply propositional_extensionality. split. lia. lia. symmetry. 
                    apply AddTrue with (mu := fst ps) (P := (\{ (x0 = n) \})) (Q := (\{ (x0 + 1) = (n + 1) \})) . easy. 
                    apply HTAsgn.
            ----------- apply HConseqLeft with (eta2 := ({{ y3 = onethird }})). uncoerce_basic. easy.
          apply RigidUnchanged.   
       ---------- apply HConseqRight with (eta2 := ({{ 0 = (prob (x0 = (n + 1))) /\ y2 = 0 }})).
          unfold PAImplies. uncoerce_basic. intros. lra. apply HAnd.
          ----------- uncoerce_basic. apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 - 1}>)  ({{0 = (prob (x0 = (n + 1)))}}))).
                    unfold PAImplies. uncoerce_basic. intros. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. simpl.
                    unfold t_update. simpl. rewrite String.eqb_refl. simpl. destruct H0.
                    pose proof (measure_P_eq_true (fst ps) ((fun st : state => n = fst st x0))) H0. simpl in H2. symmetry.
                    apply measure_inclusion_0 with (mu := fst ps) (P := (fun st : state => (n + 1)%nat = (fst st x0 - 1)%nat))
                          (Q := (fun st : state => n <> fst st x0) ). lia. easy. apply HTAsgn.
            ----------- apply HConseqLeft with (eta2 := ({{ y2 = 0 }})). easy.
          apply RigidUnchanged.      
--------- apply HAnd. apply HConseqLeft with (eta2 := (fun st : Pstate => (snd st y3) = onethird)). easy. apply RigidUnchanged.
         apply HConseqLeft with (eta2 := (fun st : Pstate => (snd st y2) = 0%R)). easy. apply RigidUnchanged.
------- unfold elsecase. apply HConseqRight with (eta2 :=  (fun st : Pstate =>
   and (eq (fst st (fun _ : state => True)) 0%R)
     (eq (snd st y2) 0%R))). 2: apply HSkip. unfold PAImplies. intros. destruct H0. rewrite H1.
     pose proof empty_measure_inclusion (fst ps). pose proof H2 H0. specialize H3 with (fun st : state => (n + 1)%nat = fst st x0). easy.
------ apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y3 = onethird /\ snd st y2 = 0%R)). unfold PAImplies.
       unfold psfBpsf. unfold PAcondB. unfold ifcase. unfold elsecase.  simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. rewrite H0. easy.
       rewrite H0. easy.
 --- assert ((eta_update_y_p ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) /\ (y2 = 0) /\ (y3 = onethird) }}) y4 (1%R)) = 
            ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) /\ (y1 = twothird) /\ (y2 = 0) /\ (y3 = onethird) }})) as Hlpr4. uncoerce_basic.
           unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy. uncoerce_basic Hlpr4. uncoerce_basic.
     eapply HConseqLeft with (eta2 := (eta_update_y_p
          (fun ps : Pstate =>
   (fst ps (fun st0 : state => n = fst st0 x0) = 1%R /\
    fst ps (fun st0 : state => n = fst st0 x0) = fst ps {{true}} /\
    snd ps y1 = twothird /\ snd ps y2 = 0%R) /\ snd ps y3 = onethird) y4 (Preal 1))). easy.
    apply HElimv. uncoerce_basic. 
    ----
         set (ifcase2 := (fun ps : Pstate =>
   ((fst ps (fun st0 : state => n = fst st0 x0) =
     1%R /\
     fst ps (fun st0 : state => n = fst st0 x0) =
     fst ps {{true}} /\
     snd ps y1 = twothird /\ snd ps y2 = 0%R) /\
    snd ps y3 = onethird) /\ snd ps y4 = 1%R) ).
         unfold GamblersRuin_Body. apply HConseq with (eta2 := (psfBpsf ifcase2  elsecase (<{x0 >= 1}>)))  (eta3 := ({{ ( (y4 + y2 = (prob true)) /\ y4 = 1) /\ y2 = 0 }})).
    ----- unfold ifcase2. unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. unfold elsecase. uncoerce_basic. intros. 
                  destruct H0. destruct H0. destruct H0. destruct H3. 
                  replace (fun st : state => n = fst st x0 /\ 1 <= fst st x0) with (fun st : state => n = fst st x0).
                  split. split. split. split. rewrite <- H0. easy. split.
                  apply Rle_antisym. apply measure_inclusion. lia. rewrite H3. apply measure_inclusion. lia. easy.
                  easy. easy. split. replace (fun st : state => True /\ ~ 1 <= fst st x0) with (fun st : state => ~ 1 <= fst st x0).
                  apply measure_P_eq_true. apply Rle_antisym. apply measure_inclusion. easy.
                  rewrite <- H3. apply measure_inclusion. lia. apply functional_extensionality. intros. apply propositional_extensionality.
                  lia. easy.
    ----- unfold PAImplies. uncoerce_basic. intros. lra.
    ----- apply HAnd. apply HAnd.
           ------ apply HIfThen.
              ------- eapply HSeq with (eta2 := ({{ ifcase2 /\((prob b) = onethird) /\ ( (prob (~b)) = twothird)}})). unfold twothird. unfold onethird.
                       uncoerce_basic. unfold CBoolexp_of_bexp.
                        eapply HConseqLeft with (eta2 := (btoss_pt b (1 / 3)%R  (fun st : Pstate => ifcase2 st /\
                                   fst st (fun st0 : state => Beval (BVar b) st0) = (1 / 3)%R /\
                                   fst st (fun st0 : state => ~ snd st0 b) = (2 / 3)%R))).
                unfold PAImplies. unfold ifcase2. intros. unfold btoss_pt. simpl. 
                unfold measure_sub_btoss. unfold measure_sub_bexp. unfold assertion_sub_bexp. simpl.
                destruct H0. destruct H0. destruct H0. destruct H3. rewrite -> H0. rewrite -> H0 in H3. rewrite <- H2. split.
                lra. unfold t_update. simpl. pose proof measure_false_is_zero (fst ps).
                rewrite <- H3. rewrite H5. split. lra.
                  assert ((fun _ : state => ~ True) = ({{false}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H6. rewrite H5.
                  assert ((fun _ : state => ~ False) = ({{true}})).
                     apply functional_extensionality. intros. apply propositional_extensionality. easy.
                rewrite H7. rewrite <- H3. lra.
        apply HBToss. uncoerce_basic.
       apply HConseqRight with (eta2 := ({{ y3 + y1 = (prob true) /\ y1 = twothird /\ y3 = onethird /\ y4 = 1}})).
      unfold PAImplies. uncoerce_basic. unfold twothird. unfold onethird. intros. destruct H0. rewrite <- H0. lra.
      apply HAnd. 
        -------- apply HConseqLeft with (eta2 := (psfBpsf ({{(prob true) = onethird  /\  y3 = onethird}}) ({{(prob true) = twothird /\ y1 = twothird}}) (<{b}>))).
            --------- unfold PAImplies. unfold ifcase2. unfold psfBpsf. unfold PAcondB. unfold Measure_cond_B. uncoerce_basic. intros. 
                      replace (fun st : state => True /\ snd st b) with (CBoolexp_of_bexp (BVar b)).
                      replace (fun st : state => True /\ ~ snd st b) with (fun st : state => ~ snd st b).
                      lra. 
                      apply functional_extensionality. intros. apply propositional_extensionality. easy.
                      apply functional_extensionality. intros. apply propositional_extensionality. easy.
        --------- apply HIfThen. 
                ---------- apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 + 1}>)  ({{ y3 = (prob true) }}))).
                           unfold PAImplies. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. uncoerce_basic. intros. lra.
                           apply HTAsgn.
                ---------- apply HConseqLeft with (eta2 := (tasgn_pt x0 (<{ x0 - 1}>)  ({{ y1 = (prob true) }}))).
                           unfold PAImplies. unfold tasgn_pt. unfold measure_sub_term. unfold assertion_sub_term. uncoerce_basic. intros. lra.
                           apply HTAsgn.  
        -------- unfold ifcase2. apply HAnd.
        --------- apply HConseqLeft with (eta2 := ({{ y1 = twothird}})). unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold ifcase2. unfold elsecase. unfold Measure_cond_B.
        uncoerce_basic. intros. lra. apply RigidUnchanged.
        --------- apply HAnd. apply HConseqLeft with (eta2 := ({{ y3 = onethird}})). unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold ifcase2. unfold elsecase. unfold Measure_cond_B.
        uncoerce_basic. intros. lra. apply RigidUnchanged.
        ---------- apply HConseqLeft with (eta2 := ({{ y4 = 1}})). unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold ifcase2. unfold elsecase. unfold Measure_cond_B.
        uncoerce_basic. intros. lra. apply RigidUnchanged.

------- unfold elsecase. apply HConseqLeft with (eta2 := ({{ y2 = (prob true)}})). unfold PAImplies. uncoerce_basic. intros. lra. apply HSkip.
------ apply HConseqLeft with (eta2 := ({{ y4 = 1}})). unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold ifcase2. unfold elsecase. unfold Measure_cond_B.
        uncoerce_basic. intros. lra. apply RigidUnchanged.
------ apply HConseqLeft with (eta2 := ({{ y2 = 0}})). unfold PAImplies. unfold psfBpsf. unfold PAcondB. unfold ifcase2. unfold elsecase. unfold Measure_cond_B.
        uncoerce_basic. intros. lra. apply RigidUnchanged.
    ---- easy.
    ---- easy.
  --- unfold p_inv_y. intros. easy.
  --- unfold eta_inv_y. intros. simpl. easy.
 --- easy.
 --- easy.
 -- easy.
 -- easy.
-- apply functional_extensionality. intros. apply propositional_extensionality. split. easy. easy.
Qed.


(* 
{{ifcase / <{ ((Var x0) >= (Const 1)) }> \ elsecase}} 
(GamblersRuin_Body x0)
{{(fun st : Pstate =>
   ((fst st (fun st0 : state => (n - 1) = (fst st0 x0))) =
    twothird) /\
   (((fst st (fun st0 : state => ((n + 1)%nat) = (fst st0 x0))) =
     onethird) /\ ((fst st {{true}}) = (1%R))))}} *)







Theorem xgeq1_m:forall (x0: string) (n : nat), (n >= 1) -> (forall (m: nat), (neq m (n-1)) -> (neq m (n+1)) ->  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ ((prob (x0 = m)) = 0)}})).
Proof.
intros. apply HConseqRight with (eta2 := ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})).
uncoerce_basic. unfold onethird. unfold twothird. unfold PAImplies. intros.
assert (((fst ps (\{ (x0 = (n - 1)) \/ (x0 = (n + 1)) \})) = 1)%R).
 - replace (fst ps (\{ (x0 = (n - 1)) \/ (x0 = (n + 1)) \})) with ((fst ps (fun st : state => (n - 1)%nat = fst st x0)) + ( fst ps (fun st : state => (n + 1)%nat = fst st x0)))%R.
     lra. uncoerce_basic. apply fin_additivity with (mu := fst ps) (P := (fun st : state => (n - 1)%nat = fst st x0)) (Q := (fun st : state => (n + 1)%nat = fst st x0)).
    intros. lia.
 - uncoerce_basic H3.  destruct H2. destruct H4. rewrite <- H5 in H3.
    apply measure_inclusion_0 with (mu := fst ps) (P:= (fun st : state => m = fst st x0)) (Q:= (fun st : state =>
        ~(n - 1 = fst st x0 \/ (n + 1)%nat = fst st x0))). intros. rewrite <- H6. unfold not. intros. destruct H7. unfold neq in H0. rewrite H7 in H0.
        contradiction. rewrite H7 in H1. contradiction. apply measure_P_eq_true with (P := (fun st : state =>
        n - 1 = fst st x0 \/ (n + 1)%nat = fst st x0)). easy.
 - uncoerce_basic. apply xgeq1. easy. 
Qed.


Theorem xgeq1_m_UB: forall (x0: string) (n m : nat), (n >= 1) -> (neq m (n-1)) -> (neq m (n+1)) ->  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ ((prob (x0 = m)) <= 0)}}).
Proof.
intros. 
apply HConseqRight with (eta2 := ({{ ((prob (x0 = m)) = 0)}})).
unfold PAImplies. intros. rewrite H2. easy. apply xgeq1_m.
easy. easy. easy.
Qed.


Theorem xgeq1_m_UB2: forall (x0: string) (n m : nat), (n >= 1) -> (m > (n +1)) ->  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ ((prob (x0 >= m)) = 0)}}).
Proof.
intros. apply HConseqRight with (eta2 := ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})).
uncoerce_basic. unfold onethird. unfold twothird. unfold PAImplies. intros.
assert (((fst ps (\{ (x0 = (n - 1)) \/ (x0 = (n + 1)) \})) = 1)%R).
 - replace (fst ps (\{ (x0 = (n - 1)) \/ (x0 = (n + 1)) \})) with ((fst ps (fun st : state => (n - 1)%nat = fst st x0)) + ( fst ps (fun st : state => (n + 1)%nat = fst st x0)))%R.
     lra. uncoerce_basic. apply fin_additivity with (mu := fst ps) (P := (fun st : state => (n - 1)%nat = fst st x0)) (Q := (fun st : state => (n + 1)%nat = fst st x0)).
    intros. lia.
 - uncoerce_basic H2.  destruct H1. destruct H3.
    apply measure_inclusion_0 with (mu := fst ps) (P:= (fun st : state => m <= fst st x0)) (Q:= (fun st : state =>
        ~(n - 1 = fst st x0 \/ (n + 1)%nat = fst st x0))). intros. unfold not. intros. destruct H6. unfold neq in H0. rewrite <- H6 in H5. lia.
         rewrite <- H6 in H5. lia.
        rewrite  <- H4 in H2. apply measure_P_eq_true with (P := (fun st : state =>
        n - 1 = fst st x0 \/ (n + 1)%nat = fst st x0)). easy.
 - uncoerce_basic. apply xgeq1. easy. 
Qed.


Theorem xgeq1_n_UB: forall (x0: string) (n: nat), (n >= 1) ->
        (hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob (x0 = (n - 1))) <= twothird) }})) /\
                (hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob (x0 =n )) <= 0) }})) /\
                (hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob (x0 = (n + 1))) <= onethird) }}))
   .
Proof.
intros. split. apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H1. destruct H0. unfold Pteval in H0. rewrite <- H0. uncoerce_basic. lra.
uncoerce_basic. apply HAnd.
apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H1. destruct H0. unfold Pteval in H0. uncoerce_basic H0. easy.
uncoerce_basic. apply xgeq1. easy.
apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H1. destruct H0. unfold Pteval in H0. easy. uncoerce_basic. apply xgeq1. easy. uncoerce_basic.
split.
apply xgeq1_m_UB with (x0 := x0) (n := n) (m := n). easy. unfold neq. intros Heq. lia. unfold neq. intros Heq. lia.
apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H0. destruct H0. unfold Pteval in H0. destruct H1. rewrite H1. lra.
uncoerce_basic. apply HAnd.
apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H0. destruct H0. unfold Pteval in H0. uncoerce_basic H0. easy.
uncoerce_basic. apply xgeq1. easy.
apply HConseqRight with (eta2 :=   ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})     ).
unfold PAImplies. intros. uncoerce_basic H1. destruct H0. unfold Pteval in H0. easy. uncoerce_basic. apply xgeq1. easy.
Qed.


Theorem xeq1_UB: forall (x0: string),
        (hoare_triple ({{ ((prob (x0 = 1)) = 1) /\ ((prob (x0 = 1)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob ( ~(x0 >= 1)  )) <= twothird) }})) /\
                (hoare_triple ({{ ((prob (x0 = 1)) = 1) /\ ((prob (x0 = 1)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob (x0 = 1 )) <= 0) }}))                                                                                                             /\
                (hoare_triple ({{ ((prob (x0 = 1)) = 1) /\ ((prob (x0 = 1)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                 ({{ ((prob (x0 = 2)) <= onethird) }}))
   .
Proof.
intros. uncoerce_basic. split.
-  apply HConseqRight with (eta2 := ({{ ((prob (x0 = 0)) = twothird) /\ ((prob (x0 = 2)) = onethird) /\ ((prob (true)) = 1)}})).
   --  uncoerce_basic. unfold PAImplies. intros. assert (\{ ~(x0 >= 1) \} = \{ x0 = 0 \}).
        apply functional_extensionality. uncoerce_basic. intros. apply propositional_extensionality. lia.
        uncoerce_basic H0. rewrite H0. lra.
   -- uncoerce_basic. apply xgeq1 with (x0 := x0) (n := 1). lia.
 - apply xgeq1_n_UB with (n := 1). lia.
Qed.




Theorem xgeq1_lt1_UB: forall (x0: string) (n : nat), (n > 1) ->  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                                                                          ({{ ((prob ( ~(x0 >= 1)  )) <= 0)}}).
Proof.
intros. uncoerce_basic. 
apply HConseqRight with (eta2 := ({{ ((prob (x0 = 0)) = 0)}})).
unfold PAImplies. uncoerce_basic. intros. rewrite <- H0. apply measure_inclusion.
lia. uncoerce_basic. apply xgeq1_m. lia. unfold neq. lia. unfold neq. lia.
Qed.





Theorem xgeq1_max: forall (x0: string) (n: nat), (n >= 1) ->  
                  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                  ({{  ((prob (x0 >= (n + 1))) = onethird) }})
              .
Proof.
intros. apply HConseqRight with (eta2 := ({{ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (x0 >= (n + 2))) = 0)}})).
- unfold PAImplies. uncoerce_basic. intros. destruct H0. replace (fun st : state => (n + 1 <= fst st x0)%nat) with (fun st : state => ((n + 1 = fst st x0)%nat) \/ (~((n + 1 >= fst st x0)%nat))).
    replace  (fst ps (fun st : state => ((n + 1 = fst st x0)%nat) \/ (~((n + 1 >= fst st x0)%nat)))) with 
           ((fst ps (fun st : state => ((n + 1 = fst st x0)%nat))) + (fst ps (fun st : state => (~((n + 1 >= fst st x0)%nat)))))%R.
    replace (fun st : state => ~ (n + 1 >= fst st x0)%nat) with  (fun st : state => (n + 2)%nat <= (fst st x0)). rewrite H0. rewrite H1.
    lra. apply functional_extensionality. intros. apply propositional_extensionality. lia. apply fin_additivity. lia.
    apply functional_extensionality. intros. apply propositional_extensionality. lia.
- apply HAnd.
 -- apply HConseqRight with (eta2 := ({{ ((prob (x0 = (n - 1))) = twothird) /\ ((prob (x0 = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})).
    easy. apply xgeq1. easy.
 -- apply xgeq1_m_UB2 with (m := (n + 2)%nat). easy. lia.
Qed.

Theorem xgeq_max_UB: forall (x0: string) (n: nat), (n >= 1) ->  
                  hoare_triple ({{ ((prob (x0 = n)) = 1) /\ ((prob (x0 = n)) = (prob true)) }}) 
                                                                            (GamblersRuin_Body x0) 
                  (fun st : Pstate =>
   ((fst st
       (fun st0 : state =>
        (~ (~ (( (n + 1) <= (fst st0 x0))%nat))) /\
        (( (n + 1) <= (fst st0 x0))%nat))) <= (1 / 3))%R).
Proof.
intros. apply HConseqRight with (eta2 := ({{  ((prob (x0 >= (n + 1))) = onethird) }})).
unfold PAImplies. uncoerce_basic. intros. unfold onethird in H0. rewrite <- H0. apply measure_inclusion.
lia.
apply xgeq1_max. easy.
Qed.


Fixpoint xlt1_1ton (max: nat) (x0 : string) (st: Pstate): Prop := 
  match max with 
    | 0 => True
    | S max => (and (xlt1_1ton max x0 st) (Rle (fst st (fun st0 : state => eq (S max) (fst st0 x0))) 0)
               )
end.


Eval cbn in (fun st => xlt1_1ton 4 x st).


(* The antecedent of the while UB rule when x < 1 *)
Theorem xlt1_ant: forall (n: nat) (x0 : string), (n >= 1) ->
hoare_triple 
  (fun st : Pstate =>
   and (eq (fst st (fun st0 : state => not (Peano.le 1 (fst st0 x0)))) 1%R)
     (eq (fst st (fun st0 : state => not (Peano.le 1 (fst st0 x0))))
        (fst st (fun _ : state => True))))
    (GamblersRuin_Body x0)
    (fun st : Pstate => 
            and 
            (and (Rle (fst st (fun st0 : state => not (Peano.le 1 (fst st0 x0)))) 1) (xlt1_1ton (n-1) x0 st))
            (Rle
              (fst st
           (fun st0 : state =>
            and (not (not (Peano.le n (fst st0 x0)))) (Peano.le n (fst st0 x0)))) 0)).
Proof.
intros. rename H into Hn.
apply HConseqRight with (eta2 := ({{ (prob ~(x0 >= 1)) = 1  /\ ((prob (true)) = 1)}})).
uncoerce_basic. unfold PAImplies. intros. split. destruct H. rewrite H. split.  easy.
induction n. simpl. easy. 
  -  destruct H. assert ( (fst ps {{true}} = ((fst ps) (\{ x0 >= 1\})) + ((fst ps) (\{ ~ (x0 >= 1) \})))%R).
    apply measure_true_dest with (mu := fst ps) (Q := (\{ x0 >= 1\})). uncoerce_basic H. rewrite H0 in H.
    assert ((((fst ps) (fun st : state => (1 <= fst st x0)%nat)) = 0)%R). lra. simpl in IHn. 
     destruct n. easy. replace (S (S n) - 1) with (S n). 2: easy. 
     simpl. split. assert (S n  >= 1). lia. pose proof IHn H2. replace  n with (S n - 1). easy. lia.
     rewrite <- H1. apply measure_inclusion. lia.
   - destruct H. assert ( (fst ps {{true}} = ((fst ps) (\{ x0 >= 1\})) + ((fst ps) (\{ ~ (x0 >= 1) \})))%R).
    apply measure_true_dest with (mu := fst ps) (Q := (\{ x0 >= 1\})). uncoerce_basic H1. rewrite H0 in H1.
    assert ((((fst ps) (fun st : state => (1 <= fst st x0)%nat)) = 0)%R). lra.
    replace (fun st0 : state => ~ ~ (n <= fst st0 x0)%nat /\ (n <= fst st0 x0)%nat) with (fun st0 : state => (n <= fst st0 x0)%nat ).
    rewrite <- H2. apply measure_inclusion. intros. lia. apply functional_extensionality. intros. apply propositional_extensionality.
    lia.
- apply xlt1.
Qed.

(* 1,2...,max *)
Fixpoint Gs_hlpr (max: nat) (i: nat) (x0: string): Vector.t Assertion max :=
  match max with
    | 0 => []
    | S n => (fun st : state => 
                eq ((CTermexp_of_nat i) st) ((CTermexp_of_Texp (Var x0)) st) ):: (Gs_hlpr n (S i) x0)
end.
Fixpoint P_i (max: nat) (i: nat): (Vector.t R (S max)) :=
  match max, i with
   | 0, _     => (const 0%R 1)
   | max , 0  => (1%R)::(const 0%R max)
   | (S 0 )  , (S 0) =>  (((2/3)%R) ::( 0%R:: []))
   | (S (S m)), (S 0) => (((2/3)%R)::((0%R)::(((1/3)%R)::(const 0%R m))))
   | (S m), (S j) => ((0%R) :: (P_i m j)) 
end.
Eval compute in P_i 2 0.
Eval compute in P_i 2 2.

Fixpoint idk (m: nat) (n: nat): (Vector.t nat n) :=
 match m, n with
  | _ , 0 => []
  | m, S n => m::( idk (S m) n)
end.
Definition _0ton (n: nat): (Vector.t nat n) := idk 0 n.
Eval compute in (_0ton 12).
Fixpoint Ts_hlpr (max: nat): Vector.t R  (S max) :=
  match max with
    | 0 => [(1/3)%R]
    | (S m) => ((0%R):: (Ts_hlpr m)) 
end.


(* <1, 1, 2...., max *)
Definition Gs (max: nat) (x0: string): Vector.t Assertion (S max) :=
     (\{ ~(x0 >= 1)  \})::(Gs_hlpr max 1 x0).

Eval cbn in Gs_hlpr 3 1 x.

(* 1,2...,max - P[i] = [0 ; 0 ... ; (i-1)->2/3 ; 0 ;  (i+1)->1/3 ; 0 ; 0...] *)
Definition Ps (max: nat): (Vector.t ( Vector.t R (S max))  (S max)):=
map (P_i max) (_0ton (S max)).
Eval cbn in (Ps 2).

(* 1,2....max - T[i] = 0 if i < max; 1/3 if max *)
Definition Ts (max: nat): Vector.t R max :=
 match max with 
    | 0 => []
    | S n => Ts_hlpr n
end.
Eval cbn in Ts 3.


Ltac uncoerce_basic_goal :=
  repeat (
uncoerce_basic; 
unfold apply_func; 
unfold inner_conj_leq; 
simpl; 
unfold gamma_leq; unfold gamma_compare
    ).



Theorem ant_1to3 (x0: string) : forall (i: nat), (i < 3) ->
(hoare_triple (List.nth i (Vector.to_list (Vector.map int_true_eq_one (Gs 2 x0))) {{true}}) 
            (GamblersRuin_Body x0) 
((List.nth i (Vector.to_list (antecedent_leq (Gs 2 x0) (Ps  2)  (<{ ~ (x0 >= 3) }>) (\{ (x0 >= 3) \}) (Ts (S 2))))) {{true}})).
Proof.
intros. unfold Gs. unfold Gs_hlpr. unfold int_true_eq_one. unfold map. unfold to_list.
destruct i.
unfold apply_func. unfold inner_conj_leq. unfold zip_gamma_leq. unfold gamma_leq. unfold gamma_compare. unfold zip_gamma_compare. uncoerce_basic. 
unfold apply_func. unfold inner_conj_leq. unfold zip_gamma_leq. unfold gamma_compare. unfold zip_gamma_compare. unfold gamma_leq. unfold gamma_compare. unfold zip.
uncoerce_basic.
 - pose proof xlt1_ant 3 x0. simpl in H0. assert (3 >= 1). lia. pose proof H0 H1.
   apply HConseqRight with (eta2 :=    (fun st : Pstate =>
        and
          (and
             (Rle
                (fst st (fun st0 : state => not (Peano.le 1 (fst st0 x0))))
                1)
             (and
                (and True
                   (Rle (fst st (fun st0 : state => eq 1 (fst st0 x0))) 0))
                (Rle (fst st (fun st0 : state => eq 2 (fst st0 x0))) 0)))
          (Rle
             (fst st
                (fun st0 : state =>
                 and (not (not (Peano.le 3 (fst st0 x0))))
                   (Peano.le 3 (fst st0 x0)))) 0))). easy.
   easy.
- destruct i. uncoerce_basic. unfold apply_func. unfold inner_conj_leq. simpl. unfold gamma_leq. unfold gamma_compare.
     uncoerce_basic. apply HAnd.
    apply HAnd. apply xeq1_UB.
    apply HAnd. apply xgeq1_m_UB with (x0 := x0)  (n := 1) (m := 1). lia. easy. easy.
    apply HConseqRight with (eta2 := ({{ (prob (x0 = 2)) <= onethird }})). easy.
    apply xgeq1_n_UB with (x0 := x0) (n := 1). lia.
    apply HConseqRight with (eta2 := ({{ (prob (x0 >= 3)) = 0 }})).
    uncoerce_basic. unfold PAImplies. intros. replace (fst ps
   (fun st : state =>
    ~ ~ (3 <= fst st x0)%nat /\ (3 <= fst st x0)%nat)) with (fst ps (fun st : state => 3 <= fst st x0)).
    lra. apply equivalence. easy. uncoerce_basic. apply xgeq1_m_UB2. lia. lia.
-- destruct i. uncoerce_basic. unfold apply_func. unfold inner_conj_leq. simpl. unfold gamma_leq. unfold gamma_compare.
     uncoerce_basic. apply HAnd.
    apply HAnd. apply xgeq1_lt1_UB. lia.
    apply HAnd. apply xgeq1_n_UB with (x0 := x0)  (n := 2). lia.
    apply HConseqRight with (eta2 := ({{ (prob (x0 = 2)) <= 0 }})). easy.
    apply xgeq1_n_UB with (x0 := x0) (n := 2). lia. 
    apply xgeq_max_UB. lia.
--- exfalso. lia.
Qed.


Check
hoare_triple
  (fun st : Pstate =>
   and (eq (fst st (fun st0 : state => eq 2 (fst st0 x))) 1%R)
     (eq (fst st (fun st0 : state => eq 2 (fst st0 x)))
        (fst st (fun _ : state => True)))) (GamblersRuin_Body x)
  (fun ps : Pstate =>
   and
     (and (Rle (fst ps (fun st : state => not (Peano.le 1 (fst st x)))) 0)

        (and (Rle (fst ps (fun st : state => eq 2 (fst st x))) 0)
           (and
              (Rle (fst ps (fun st : state => eq 1 (fst st x))) (Rdiv 2 3))
              True)))
     (Rle
        (fst ps
           (fun st : state =>
            and (not (not (Peano.le 3 (fst st x))))
              (Peano.le 3 (fst st x)))) (Rdiv 1 3))).



Definition GamblersRuin (max : nat) : Cmd :=
While (<{ ~ (x >= max) }>) (GamblersRuin_Body x).

(* Gamblers Ruin - Non Parameterized start x = 1;  Goal 3 *)
(* xi = (1 - 2^i)/ ( 1 - 2 ^ N) *)
(*  x1 = 1/7; x2 = 3/7 *)

Definition seventh := (1/7)%R.
 
Definition y: string := "y".


Theorem Gambler3_UB: hoare_triple ({{ ((prob (x = 1)) = y) /\ ((prob (x = 1)) =  (prob true)) /\ y = 1 }}) (GamblersRuin 3) ({{ (prob (x >= 3)) <= seventh}}).
Proof.
uncoerce_basic.
(* flip G and P *)
set (G := (Gs 2 x)). uncoerce_basic G.
set (P :=  (Ps  2)).
set (T := (Ts (S 2))).
set (gamma := (\{ (x >= 3) \})).
set (beta := <{ ~ (x >= 3) }>).
set (tempAssertion := <{ (x = 1) }>).
assert (Xeq: forall n: nat, n < 3 -> ( (fun st : state => ~(3 <= fst st x)%nat /\ n = fst st x) = (fun st : state =>  n = fst st x))).
intros. apply functional_extensionality. intros. apply propositional_extensionality. split. easy. split. rewrite <- H0. unfold not. lia. easy. 
    
apply HConseq with (eta2 := ({{(((prob (beta /\ tempAssertion)) <= y) /\ ((prob (beta /\ tempAssertion)) = (prob true))) /\ y = 1 }}))
                   (eta3 := {{((prob gamma) <= (seventh*y)) /\ y = 1 }}).
 - uncoerce_basic. unfold PAImplies. intros. split.
    -- assert ((fun st : state => ~ (3 <= fst st x)%nat /\ 1%nat = fst st x) = (fun st : state => 1 = fst st x)).
       apply Xeq. lia.
   rewrite -> H0. destruct H.  rewrite -> H. split. easy. destruct H1. rewrite <- H1. easy.
 -- assert ((fun st : state => ~ (3 <= fst st x)%nat /\ 1%nat = fst st x) = (fun st : state => 1 = fst st x)).
       apply Xeq. lia. destruct H. rewrite -> H in H1. easy.
-  unfold gamma. uncoerce_basic. unfold PAImplies. intros. destruct H. rewrite -> H0 in H. assert ((seventh*1 = seventh)%R). lra.
   rewrite <- H1. easy.
- uncoerce_basic. apply AddRigidBoth. unfold GamblersRuin.
eapply HWhileUB with (i:= 1) (m := 3) (beta := beta) (gamma := gamma) (G := G) (P := P) (T := T) (X := [ 0%R  ; (1/7)%R ;  (3/7)%R]) .
 -- uncoerce_basic. lia.
 -- apply ant_1to3.
 -- intros. destruct i. unfold lin_ineq. simpl. lra.
            destruct i. unfold lin_ineq. simpl. lra.
            destruct i. unfold lin_ineq. simpl. lra. 
            exfalso. lia.
  -- lia. 
  -- intros. simpl. split. easy. easy.
  -- simpl. lra.
Qed.






   
