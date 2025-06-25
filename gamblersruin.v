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



Definition GamblersRuin_Body : Cmd :=
<{
if (x >= 1) 
then (b toss ((1/3)%R);
      (if b then (x := x + 1) else (x := x - 1) end))
else skip
end
}>.

(* Want to prove ->  From x -> 2/3 chance of x-1 and 1/3 chace of x+` *)
Check \{ (x<=1)\}.


(*  Gamblers Ruin Helper theorems     *)

Theorem xlt1_Else: ( forall y1 : string,  hoare_triple ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }}) <{skip}> ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }}) ).
Proof.
  - intros. apply HSkip.
Qed.


Theorem xlt1_If: ( forall y2 : string,  hoare_triple ({{((prob true) = 0) /\ (y2 = 0) }}) <{(b toss ((1/3)%R); (if b then (x := x + 1) else (x := x - 1) end))}> 
      ({{ (0 = (prob ~(x >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }}) ).
Proof.
intros. apply AddRigidRight.
 eapply HConseq with (eta1 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta2 := ({{((prob true) = 0) /\ (y2 = 0) }}))
                             (eta3 := ({{((prob true) = 0) /\ (y2 = 0) }})).
 - easy. 
 - unfold PAImplies. intros. destruct H. uncoerce_basic. split. uncoerce_basic H. uncoerce_basic H0. symmetry. apply empty_measure_inclusion2 with (mu := fst ps) (P := (fun st : state => ~ 1 <= fst st x)).
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
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x (<{x + 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
                  easy. unfold eta. unfold PAImplies. intros. destruct H. rewrite -> H. assumption. apply HTAsgn.
      ---- eapply HConseq with (eta1 := eta) (eta2 := (tasgn_pt x (<{x  - 1}>) eta)) (eta3 := eta) (eta4 := (fun ps : Pstate => (snd ps y2) = (fst ps {{true}}))).
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


Theorem xlt1:  hoare_triple ({{ ((prob ~(x >= 1)) = 1) /\ ((prob ~(x >= 1)) = (prob true)) }}) 
                                                                            GamblersRuin_Body 
                                                                          ({{ (prob ~(x >= 1)) = 1  /\ ((prob (true)) = 1)}}).
Proof.
uncoerce_basic. 
eapply HElimv with (y := y1) (p :=  (Preal 1%R)) (eta1 := ({{ ((prob ~(x >= 1)) = 1) /\ ((prob ~(x >= 1)) = (prob true)) }})).
 - uncoerce_basic.
   eapply HElimv with (y := y2) (p :=  (Preal 0%R)) (eta1 := ({{(((prob ~(x >= 1)) = 1) /\ ((prob ~(x >= 1)) = (prob true)) ) /\ (y1 = 1) }})).
    -- uncoerce_basic. Check  <{ x >= 1 }>.
       eapply HConseq with (eta2 := (psfBpsf ({{((prob true) = 0) /\ (y2 = 0) }}) ({{((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true)) /\ (y1 = 1) }}) (<{ x >= 1 }>))) 
                    (eta3 :=  ({{ (y2 + y1 = (prob ~(x >=1)) /\ y1 = 1 /\ y2 = 0) /\ (y2 + y1 = (prob true) /\ y1 = 1 /\ y2 = 0)  }})).
        --- uncoerce_basic. unfold PAImplies. intros. unfold psfBpsf. split. unfold PAcondB. simpl. split. unfold Measure_cond_B. simpl. 
            replace (fun st : state => True /\ 1 <= fst st x) with (fun st : state => 1 <= fst st x).
            pose proof measure_true_dest (fst ps) (fun st : state => 1 <= fst st x).
            destruct H. destruct H. destruct H. rewrite -> H in H3. rewrite <- H3 in H0. rewrite H in H0. lra.
            apply functional_extensionality. intros. apply propositional_extensionality. easy.
            easy.
           unfold PAcondB. simpl. split. unfold Measure_cond_B. simpl. replace (fun st : state => ~ 1 <= fst st x /\ ~ 1 <= fst st x) with (fun st : state => ~ 1 <= fst st x).
           easy. apply functional_extensionality. intros. apply propositional_extensionality. split. intros. split. easy. easy.
           easy. unfold Measure_cond_B. simpl. split. apply equivalence. easy. easy.
    --- uncoerce_basic. unfold PAImplies. intros. destruct H. destruct H0. destruct H1. rewrite H1 in H0. rewrite H2 in H0. replace 1%R with (0 + 1)%R. rewrite H1 in H. rewrite H2 in H.  easy. lra.
    --- uncoerce_basic. apply HAnd.
        apply HAnd.
        apply HIfThen.
       ---- apply HConseqRight with (eta2 := ({{ (0 = (prob ~(x >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }})).
            unfold PAImplies. intros. simpl in H. destruct H. destruct H. rewrite H0. easy.
            apply xlt1_If.
       ---- apply HConseq with (eta2 := ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }}))
                               (eta3 := ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }})).
             easy.
            unfold PAImplies. intros. simpl in H. destruct H. destruct H. rewrite H0. easy.
            simpl. apply xlt1_Else.
       ---- apply HAnd.
        ----- apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y1 = 1%R)). unfold PAImplies. unfold psfBpsf. unfold PAcondB.
              simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. intros. rewrite <- H. easy. intros. rewrite H. easy.
        ----- apply HConseqLeft with (eta2 := (fun st : Pstate => snd st y2 = 0%R)). unfold PAImplies. unfold psfBpsf. unfold PAcondB.
              simpl. intros. easy. apply HFree. unfold is_analytical. intros. split. intros. rewrite <- H. easy. intros. rewrite H. easy.
       ---- apply HAnd. apply HIfThen. apply HConseq with (eta2 := ({{((prob true) = 0) /\ (y2 = 0) }})) (eta3 := ({{ (0 = (prob ~(x >=1)) /\ ((prob (true)) = 0)) /\ (y2 = 0) }})).
             easy. simpl. unfold PAImplies. intros. destruct H. destruct H. rewrite H0. easy. simpl. apply xlt1_If.
             apply HConseq with (eta2 := ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }})) (eta3 := ({{(((prob  ~(x>=1)) = 1) /\ ((prob  ~(x>=1)) = (prob true))) /\ (y1 = 1) }})).
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


(* chain the above two usinf HIfThen and get the actual rule to be used in the while proof *)
Theorem xgeq1:forall (n: nat), (n >= 1) ->  hoare_triple ({{ ((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true)) }}) 
                                                                            GamblersRuin_Body 
                                                                          ({{ ((prob (x = (n - 1))) = twothird) /\ ((prob (x = (n + 1))) = onethird) /\ ((prob (true)) = 1)}})
              .
Proof.
intros. uncoerce_basic.
assert (\{ (x = n) /\ (1 <= x) \} = \{ (x = n) \}) as G. uncoerce_basic. apply functional_extensionality. intros. unfold CTermexp_of_nat. unfold CTermexp_of_Texp. simpl. apply propositional_extensionality.
split. easy. split. easy. rewrite <- H0. easy. uncoerce_basic G. set (ifcase := ({{ (((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true))) /\ (y1 = twothird) }})). uncoerce_basic ifcase.
set (elsecase := ({{((prob true) = 0) /\ (y2 = 0) }})).  uncoerce_basic elsecase.
assert ((eta_update_y_p ({{ ((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true)) }}) y1 twothird) = ({{ ((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true)) }})) as Hlpr. uncoerce_basic.
 - unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy.
- uncoerce_basic Hlpr. rewrite <- Hlpr. apply HElimv.
  -- (* Main proof. *)
     assert ((eta_update_y_p ({{ ((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true)) /\ (y1 = twothird) }}) y2 (0%R)) = ({{ ((prob (x = n)) = 1) /\ ((prob (x = n)) = (prob true)) /\ (y1 = twothird) }})) as Hlpr2. uncoerce_basic. 
     unfold eta_update_y_p. simpl. apply functional_extensionality. intros. easy. uncoerce_basic Hlpr2. uncoerce_basic.
     eapply HConseqLeft with (eta2 := (eta_update_y_p
          (fun st : Pstate =>
           fst st (fun st0 : state => n = fst st0 x) = 1%R /\
           fst st (fun st0 : state => n = fst st0 x) = fst st {{true}} /\
           snd st y1 = twothird) y2 (Preal 0))). rewrite <- Hlpr2. easy.
    apply HElimv. uncoerce_basic.
       eapply HConseqLeft with (eta2 :=  (psfBpsf ifcase elsecase (<{x >= 1}>))) 
         (eta1 :=  (fun ps : Pstate => (fst ps (fun st0 : state => n = fst st0 x) = 1%R /\ fst ps (fun st0 : state => n = fst st0 x) = fst ps {{true}} /\ snd ps y1 = twothird) /\ snd ps y2 = 0%R)). 
  --- simpl. unfold PAImplies. intros. uncoerce_basic H0. unfold psfBpsf. split. split. unfold Measure_cond_B. simpl. split. rewrite -> G. easy.
   rewrite G. destruct H0. destruct H0. rewrite H0. 
   pose proof  measure_inclusion_true (fst ps) (fun st : state => True /\ 1 <= fst st x). unfold assert_of_Prop in H3. destruct H2. rewrite <- H2 in H3. rewrite -> H0 in H3.
   pose proof measure_inclusion (fst ps) (fun st : state => n = fst st x)  (fun st : state => True /\ 1 <= fst st x).
   assert (forall st : state, (fun st0 : state => n = fst st0 x) st -> (fun st0 : state => True /\ 1 <= fst st0 x) st).
   intros. split. easy. rewrite <- H6. easy. pose proof H5 H6. rewrite H0 in H7. apply Rle_antisym. easy. easy.
   ---- destruct H0. destruct H0. simpl. easy.
 ---- unfold PAcondB. unfold elsecase. simpl. unfold Measure_cond_B. simpl. split.
        ----- admit. (* TODO: prob ( 1 <= x) = prob (true) = 1. Rewrite using G H0;  split true wrt  1 <= x. 
                         1 + prob( ~ 1 <= x) = 1. conclude the goal. *)
        ----- easy.
 --- (* If Then Else stuff - split into 3 cases. one for consluding n-1, n+1, and finally total measure *)
      apply HAnd.
      eapply HConseqRight with (eta2 :=  ({{ y1 + y2 = (prob (x = (n - 1))) /\ y1 = twothird /\ y2 = 0}})).
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
------- uncoerce_basic.
          admit.

------ unfold elsecase. admit.
----- admit.
---- admit.
  --- unfold p_inv_y. intros. easy.
  --- unfold eta_inv_y. intros. simpl. easy.
 -- easy.
 -- easy.
Admitted.

Check \{ x = 1\}.


Definition GamblersRuin (max : nat) : Cmd :=
While (<{ ~ (x >= max) }>) GamblersRuin_Body.

(* Gamblers Ruin - Non Parameterized start x = 1;  Goal 3 *)
(* xi = (1 - 2^i)/ ( 1 - 2 ^ N) *)
(*  x1 = 1/7; x2 = 3/7 *)

Definition seventh := (1/7)%R.
 
Definition y: string := "y".

Theorem Gambler3_UB: hoare_triple ({{ ((prob (x = 1)) = y) /\ ((prob (x = 1)) =  (prob true)) /\ y = 1 }}) (GamblersRuin 3) ({{ (prob (x >= 3)) <= seventh}}).
Proof.
uncoerce_basic.
set (G := ([ (\{ ~(x >= 1)  \}) ; (\{ x = 1  \});(\{ x = 2 \})])). uncoerce_basic G.
set (P :=  [ [ 1%R  ; 0%R     ;  0%R ];
             [ 0%R  ; 0%R     ;  (1/3)%R ];
             [ 0%R  ; (2/3)%R ;  0%R ]
           ]).
set (T := [ 0%R ; 0%R ; (1/3)%R]).
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
 -- intros. destruct i. 
    ---- simpl. unfold int_true_eq_one. uncoerce_basic. unfold apply_func. unfold G. unfold inner_conj_leq. simpl. unfold gamma_leq.
         unfold gamma_compare. uncoerce_basic.
    apply HAnd. apply HAnd.
     ----- apply HConseqRight with (eta2 :=  ({{ (prob ~(x >= 1)) = 1}})).
           uncoerce_basic. unfold PAImplies. intros. rewrite -> H0. easy. apply HConseqRight with (eta2 :=  ({{ (prob ~(x >= 1)) = 1  /\ ((prob (true)) = 1)}})). 
           unfold PAImplies. intros. easy. apply xlt1.
     ----- apply HConseqRight with (eta2 :=  ({{ (prob ~(x >= 1)) = 1  /\ ((prob (true)) = 1)}})).
           unfold PAImplies. simpl. uncoerce_basic. intros. pose proof measure_true_dest (fst ps) (\{ x >= 1 \}) as H2.
           destruct H0. rewrite H1 in H2. uncoerce_basic H2. assert ((fun st : state => ~ 1 <= fst st x) = (fun st : state => ~ (1 <= fst st x)%nat)).
            easy. rewrite H0 in H2. split. assert (((fst ps (fun st : state => (1 <= fst st x)%nat)) = 0)%R). lra.
            assert (((fst ps (fun st : state => 1%nat = fst st x)) <= (fst ps (fun st : state => (1 <= fst st x)%nat)))%R). 
            apply measure_inclusion with (mu := (fst ps)) (P := (fun st : state => 1%nat = fst st x)) (Q :=  (fun st : state => (1 <= fst st x)%nat)). intros. lia.
            rewrite <- H4. easy. split. assert (((fst ps (fun st : state => (1 <= fst st x)%nat)) = 0)%R). lra. assert (((fst ps (fun st : state => 2%nat = fst st x)) <= (fst ps (fun st : state => (1 <= fst st x)%nat)))%R).        
            apply measure_inclusion with (mu := (fst ps)) (P := (fun st : state => 2%nat = fst st x)) (Q :=  (fun st : state => (1 <= fst st x)%nat)). intros. lia.
            transitivity (fst ps (fun st : state => (1 <= fst st x)%nat)). easy.
            rewrite H4. lra. easy. uncoerce_basic. 
      ------ admit. ----- admit. ---- admit.
 -- intros. destruct i. unfold lin_ineq. simpl. lra.
            destruct i. unfold lin_ineq. simpl. lra.
            destruct i. unfold lin_ineq. simpl. lra.
            exfalso. lia.
  -- lia. 
  -- intros. simpl. split. easy. easy.
  -- simpl. lra.
Admitted.
       

Fixpoint Gvec (n : nat) : (Vector.t Assertion n) := 
  match n with
    | 0 => []
    | S m => (\{ x = m  \})::(Gvec m) (* n-1 ---> 0 *)
end.


Theorem GamblersRuin_Body_Stuck: hoare_triple (int_true_eq_one \{ ~(x<=1)\}) GamblersRuin_Body ({{ (prob ~(x <=1)) = 1}}).
Proof.
unfold GamblersRuin_Body. eapply HConseq.

