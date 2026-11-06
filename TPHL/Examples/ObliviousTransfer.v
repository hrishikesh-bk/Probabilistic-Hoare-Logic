(** Oblivious transfer (ported from the old [ObliviousTransfer.v]).

    The receiver's choice bit [c] is hidden by a fair mask [d]: what the
    sender sees, [(r0, r1, e)] with [e := c xor d], is independent of [c]. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module ObliviousTransfer.

Notation r0 := (bool_program_var "r0").
Notation r1 := (bool_program_var "r1").
Notation c := (bool_program_var "c").
Notation d := (bool_program_var "d").
Notation e := (bool_program_var "e").

Definition ObliviousTransfer : Cmd :=
  <{ r0 toss 0.5; r1 toss 0.5; d toss 0.5; e b= ((c /\ ~ d) \/ (~ c /\ d)) }>.

Theorem OT_Input_Indep (w x y z : bool) :
  hoare_derivable {{ (prob true) = 1 }} ObliviousTransfer
    {{ (prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z)))
       = (prob (c <-> w)) * (prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) }}.
Proof.
  unfold ObliviousTransfer.
  apply HSeq with (eta2 := {{ (prob ((c <-> w) /\ (r0 <-> x))) = (prob (c <-> w)) * (prob (r0 <-> x)) }}).
  - apply HConseqLeft with (pre' := toss_pformula r0 0.5
      {{ (prob ((c <-> w) /\ (r0 <-> x))) = (prob (c <-> w)) * (prob (r0 <-> x)) }}).
    + destruct w, x; pauto [fvar c].
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HSeq with (eta2 :=
      {{ (prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y)))
         = (prob (c <-> w)) * (prob ((r0 <-> x) /\ (r1 <-> y))) }}).
    + apply HConseqLeft with (pre' := toss_pformula r1 0.5
        {{ (prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y)))
           = (prob (c <-> w)) * (prob ((r0 <-> x) /\ (r1 <-> y))) }}).
      * destruct w, x, y; pauto [fvar c; fvar r0].
      * apply HBoolToss. unfold coin_probability_valid; lra.
    + apply HSeq with (eta2 := subst_bool_pformula e \{ (c /\ ~ d) \/ (~ c /\ d) \}
        {{ (prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z)))
           = (prob (c <-> w)) * (prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) }}).
      * apply HConseqLeft with (pre' := toss_pformula d 0.5
          (subst_bool_pformula e \{ (c /\ ~ d) \/ (~ c /\ d) \}
            {{ (prob ((c <-> w) /\ (r0 <-> x) /\ (r1 <-> y) /\ (e <-> z)))
               = (prob (c <-> w)) * (prob ((r0 <-> x) /\ (r1 <-> y) /\ (e <-> z))) }})).
        -- destruct w, x, y, z; pauto [fvar c; fvar r0; fvar r1].
        -- apply HBoolToss. unfold coin_probability_valid; lra.
      * apply HBoolAssign.
Qed.

End ObliviousTransfer.
