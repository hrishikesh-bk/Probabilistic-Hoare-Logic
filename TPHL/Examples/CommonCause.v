(** Common cause (ported from the old [CommonCause.v]).

    Three fair coins [x], [y], [z]; [a := x \/ z] and [b := y \/ z].  Then [a]
    and [b] are independent given [z]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module CommonCause.

Notation x := (bool_program_var "x").
Notation y := (bool_program_var "y").
Notation z := (bool_program_var "z").
Notation a := (bool_program_var "a").
Notation b := (bool_program_var "b").

Definition CommonCause : Cmd :=
  <{ x toss (1/2); y toss (1/2); z toss (1/2); a b= (x \/ z); b b= (y \/ z) }>.

Notation hf := (pconst (1/2)).
Notation fth := (pconst (1/4)).
Notation eth := (pconst (1/8)).

(** The proof follows the old one rule by rule: a consequence step to a
    closed form, then one [HSeq] per command, each toss and assignment by
    [HConseqLeft] onto its transformer ([toss_pformula] = old [btoss_pt],
    [subst_bool_pformula] = old [basgn_pt]) and the leaf rule. *)
Theorem CommonCauseCondIndep (k1 k2 k3 : bool) :
  hoare_derivable
    {{ (prob true) = 1 }}
    CommonCause
    {{ (prob ((a <-> k1) /\ (b <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
       = (prob ((a <-> k1) /\ (z <-> k3))) * (prob ((b <-> k2) /\ (z <-> k3))) }}.
Proof.
  unfold CommonCause.
  eapply HConseqLeft with (pre' :=
    {{ (hf * (prob (k1 /\ k2 /\ k3)) + eth * (prob (~ k3))) * (hf * (prob true))
       = (hf * (prob (k1 /\ k3)) + fth * (prob (~ k3)))
         * (hf * (prob (k2 /\ k3)) + fth * (prob (~ k3))) }}).
  { destruct k1, k2, k3; pauto (@nil CFormula). }
  eapply HSeq with (eta2 :=
    {{ (hf * (prob (k1 /\ k2 /\ k3)) + fth * (prob ((x <-> k1) /\ ~ k3))) * (hf * (prob true))
       = (hf * (prob (k1 /\ k3)) + hf * (prob ((x <-> k1) /\ ~ k3)))
         * (hf * (prob (k2 /\ k3)) + fth * (prob (~ k3))) }}).
  - eapply HConseqLeft with (pre' := toss_pformula x (1/2)
      {{ (hf * (prob (k1 /\ k2 /\ k3)) + fth * (prob ((x <-> k1) /\ ~ k3))) * (hf * (prob true))
         = (hf * (prob (k1 /\ k3)) + hf * (prob ((x <-> k1) /\ ~ k3)))
           * (hf * (prob (k2 /\ k3)) + fth * (prob (~ k3))) }}).
    + destruct k1, k2, k3; pauto (@nil CFormula).
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - eapply HSeq with (eta2 :=
      {{ (hf * (prob (k1 /\ k2 /\ k3)) + hf * (prob ((x <-> k1) /\ (y <-> k2) /\ ~ k3)))
           * (hf * (prob true))
         = (hf * (prob (k1 /\ k3)) + hf * (prob ((x <-> k1) /\ ~ k3)))
           * (hf * (prob (k2 /\ k3)) + hf * (prob ((y <-> k2) /\ ~ k3))) }}).
    + eapply HConseqLeft with (pre' := toss_pformula y (1/2)
        {{ (hf * (prob (k1 /\ k2 /\ k3)) + hf * (prob ((x <-> k1) /\ (y <-> k2) /\ ~ k3)))
             * (hf * (prob true))
           = (hf * (prob (k1 /\ k3)) + hf * (prob ((x <-> k1) /\ ~ k3)))
             * (hf * (prob (k2 /\ k3)) + hf * (prob ((y <-> k2) /\ ~ k3))) }}).
      * destruct k1, k2, k3; pauto [fvar x].
      * apply HBoolToss. unfold coin_probability_valid; lra.
    + eapply HSeq with (eta2 :=
        {{ (prob (((x \/ z) <-> k1) /\ ((y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
           = (prob (((x \/ z) <-> k1) /\ (z <-> k3))) * (prob (((y \/ z) <-> k2) /\ (z <-> k3))) }}).
      * eapply HConseqLeft with (pre' := toss_pformula z (1/2)
          {{ (prob (((x \/ z) <-> k1) /\ ((y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
             = (prob (((x \/ z) <-> k1) /\ (z <-> k3)))
               * (prob (((y \/ z) <-> k2) /\ (z <-> k3))) }}).
        -- destruct k1, k2, k3; pauto [fvar x; fvar y].
        -- apply HBoolToss. unfold coin_probability_valid; lra.
      * eapply HConseqLeft with (pre' := subst_bool_pformula a \{ x \/ z \}
          {{ (prob ((a <-> k1) /\ ((y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
             = (prob ((a <-> k1) /\ (z <-> k3))) * (prob (((y \/ z) <-> k2) /\ (z <-> k3))) }}).
        -- destruct k1, k2, k3; pauto [fvar x; fvar y; fvar z].
        -- eapply HSeq with (eta2 :=
             {{ (prob ((a <-> k1) /\ ((y \/ z) <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
                = (prob ((a <-> k1) /\ (z <-> k3))) * (prob (((y \/ z) <-> k2) /\ (z <-> k3))) }}).
           ++ apply HBoolAssign.
           ++ eapply HConseqLeft with (pre' := subst_bool_pformula b \{ y \/ z \}
                {{ (prob ((a <-> k1) /\ (b <-> k2) /\ (z <-> k3))) * (prob (z <-> k3))
                   = (prob ((a <-> k1) /\ (z <-> k3))) * (prob ((b <-> k2) /\ (z <-> k3))) }}).
              ** destruct k1, k2, k3; pauto [fvar a; fvar y; fvar z].
              ** apply HBoolAssign.
Qed.

End CommonCause.
