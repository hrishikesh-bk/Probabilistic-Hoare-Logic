(** Soundness of TPHL (Theorem 10): every derivable triple is valid.  The
    proof is an induction on derivations; each rule is discharged by its
    [hoare_valid_*] lemma. *)
From Stdlib Require Import Reals.
Require Import PHL.
Require Import Soundness.StructuralRules Soundness.AtomicRules Soundness.SplitRules
  Soundness.WhileNonentry Soundness.WhileUpper Soundness.WhileLower.

Section Soundness.
Context {D : Domain}.

Theorem hoare_derivable_sound (pre : PFormula D) (c : Cmd D) (post : PFormula D) :
  hoare_derivable pre c post -> hoare_valid pre c post.
Proof.
  induction 1.
  - apply hoare_valid_free; assumption.
  - apply hoare_valid_skip.
  - apply hoare_valid_dom_assign.
  - apply hoare_valid_bool_assign.
  - apply hoare_valid_bool_toss; assumption.
  - apply hoare_valid_bool_toss_invalid; assumption.
  - eapply hoare_valid_seq; eassumption.
  - eapply hoare_valid_conseq; eassumption.
  - apply hoare_valid_or; assumption.
  - apply hoare_valid_and; assumption.
  - eapply hoare_valid_elimv; eassumption.
  - apply hoare_valid_if_le; assumption.
  - apply hoare_valid_if_ge; assumption.
  - apply hoare_valid_while_not.
  - eapply hoare_valid_while_upper; eassumption.
  - eapply hoare_valid_while_lower; eassumption.
  - apply hoare_valid_sum_le; assumption.
  - apply hoare_valid_sum_ge; assumption.
Qed.

(** The same statement unpacked over an explicit measure and assignment. *)
Corollary hoare_derivable_sound_at (pre : PFormula D) (c : Cmd D) (post : PFormula D)
    (mu : Measure D) (rho : ProbLogicVar -> R) :
  hoare_derivable pre c post -> Subprob mu ->
  psatisfies {| pstate_measure := mu; pstate_prob_logic_values := rho |} pre ->
  psatisfies (CommandSemantics.run c
                {| pstate_measure := mu; pstate_prob_logic_values := rho |}) post.
Proof.
  intros H hmu hpre.
  exact (hoare_derivable_sound pre c post H
           {| pstate_measure := mu; pstate_prob_logic_values := rho |} hmu hpre).
Qed.

End Soundness.
