(** The completeness interface (App. D, Lemma 25).  A certificate for a
    command [C] is a preterm transformer [T_C] that maps every classical
    formula [gamma] to a probability term [T_C gamma] such that
      - [T_C gamma] mentions no probabilistic logic variable,
      - [T_C gamma] evaluated before [C] is the mass of [gamma] after [C],
      - [|- {y = T_C gamma} C {y = Pr(gamma)}] for every [y].
    Adapted from CPHL's Completeness/Interface.v, with measure terms in
    place of expectations. *)
Require Import PHL.

Section Interface.
Context {D : Domain}.

Definition transformer_no_prob_vars (T_C : CFormula D -> Pterm D) : Prop :=
  forall gamma y, ~ prob_logic_var_occurs_pterm y (T_C gamma).

Definition transformer_correct (C : Cmd D) (T_C : CFormula D -> Pterm D) : Prop :=
  forall ps gamma, pstate_admissible ps ->
    pterm_eval (T_C gamma) ps = pterm_eval (PProb gamma) (CommandSemantics.run C ps).

Definition transformer_derivable (C : Cmd D) (T_C : CFormula D -> Pterm D) : Prop :=
  forall gamma y,
    hoare_derivable (p_eq (PVar y) (T_C gamma)) C (p_eq (PVar y) (PProb gamma)).

Record certificate (C : Cmd D) (T_C : CFormula D -> Pterm D) : Prop := {
  certificate_no_prob_vars : transformer_no_prob_vars T_C;
  certificate_correct : transformer_correct C T_C;
  certificate_derivable : transformer_derivable C T_C
}.

End Interface.
