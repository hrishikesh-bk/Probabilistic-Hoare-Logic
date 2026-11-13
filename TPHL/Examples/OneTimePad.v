(** One-time pad.

    [b] is a fair key bit and [c := m xor b].  The ciphertext is independent
    of the message, for one bit and for two bits encrypted with fresh keys. *)
From Stdlib Require Import Reals Lra Lia Strings.String Lists.List.
Require Import PHL Examples.Lib Examples.PrAtoms.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.
Import ListNotations.

Module OneTimePad.

Notation m := (bool_program_var "m").
Notation c := (bool_program_var "c").
Notation b := (bool_program_var "b").
Notation m1 := (bool_program_var "m1").
Notation c1 := (bool_program_var "c1").
Notation m2 := (bool_program_var "m2").
Notation c2 := (bool_program_var "c2").

Definition OneTimePad : Cmd :=
  <{ b toss 0.5; c b= ((m /\ ~ b) \/ (~ m /\ b)) }>.

Theorem OTP_Input_Indep (x y : bool) :
  hoare_derivable {{ (prob true) = 1 }} OneTimePad
    {{ (prob ((c <-> x) /\ (m <-> y))) = (prob (c <-> x)) * (prob (m <-> y)) }}.
Proof.
  unfold OneTimePad.
  apply HSeq with (eta2 :=
    {{ (prob ((((m /\ ~ b) \/ (~ m /\ b)) <-> x) /\ (m <-> y)))
       = (prob (((m /\ ~ b) \/ (~ m /\ b)) <-> x)) * (prob (m <-> y)) }}).
  - apply HConseqLeft with (pre' := toss_pformula b 0.5
      {{ (prob ((((m /\ ~ b) \/ (~ m /\ b)) <-> x) /\ (m <-> y)))
         = (prob (((m /\ ~ b) \/ (~ m /\ b)) <-> x)) * (prob (m <-> y)) }}).
    + destruct x, y; pauto [fvar m].
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := subst_bool_pformula c \{ (m /\ ~ b) \/ (~ m /\ b) \}
      {{ (prob ((c <-> x) /\ (m <-> y))) = (prob (c <-> x)) * (prob (m <-> y)) }}).
    + destruct x, y; pauto [fvar m; fvar b].
    + apply HBoolAssign.
Qed.

Definition OneTimePad_2bit : Cmd :=
  <{ (b toss 0.5; c1 b= ((m1 /\ ~ b) \/ (~ m1 /\ b)));
     (b toss 0.5; c2 b= ((m2 /\ ~ b) \/ (~ m2 /\ b))) }>.

Lemma first_bit (x1 y1 y2 : bool) :
  hoare_derivable {{ (prob true) = 1 }}
    <{ b toss 0.5; c1 b= ((m1 /\ ~ b) \/ (~ m1 /\ b)) }>
    {{ (prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob (c1 <-> x1)) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}.
Proof.
  apply HSeq with (eta2 :=
    {{ (prob ((((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob (((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1)) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
  - apply HConseqLeft with (pre' := toss_pformula b 0.5
      {{ (prob ((((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2)))
         = (prob (((m1 /\ ~ b) \/ (~ m1 /\ b)) <-> x1))
           * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
    + destruct x1, y1, y2; pauto [fvar m1; fvar m2].
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := subst_bool_pformula c1 \{ (m1 /\ ~ b) \/ (~ m1 /\ b) \}
      {{ (prob ((c1 <-> x1) /\ ((m1 <-> y1) /\ (m2 <-> y2))))
         = (prob (c1 <-> x1)) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
    + destruct x1, y1, y2; pauto [fvar m1; fvar m2; fvar b].
    + apply HBoolAssign.
Qed.

Lemma second_bit (x1 x2 y1 y2 : bool) :
  hoare_derivable
    {{ (prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob (c1 <-> x1)) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}
    <{ b toss 0.5; c2 b= ((m2 /\ ~ b) \/ (~ m2 /\ b)) }>
    {{ (prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob ((c1 <-> x1) /\ (c2 <-> x2))) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}.
Proof.
  apply HSeq with (eta2 :=
    {{ (prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2)))
         * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
  - apply HConseqLeft with (pre' := toss_pformula b 0.5
      {{ (prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2) /\ (m1 <-> y1)
                /\ (m2 <-> y2)))
         = (prob ((c1 <-> x1) /\ (((m2 /\ ~ b) \/ (~ m2 /\ b)) <-> x2)))
           * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
    + destruct x1, x2, y1, y2; pauto [fvar c1; fvar m1; fvar m2].
    + apply HBoolToss. unfold coin_probability_valid; lra.
  - apply HConseqLeft with (pre' := subst_bool_pformula c2 \{ (m2 /\ ~ b) \/ (~ m2 /\ b) \}
      {{ (prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2)))
         = (prob ((c1 <-> x1) /\ (c2 <-> x2))) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
    + destruct x1, x2, y1, y2; pauto [fvar c1; fvar m1; fvar m2; fvar b].
    + apply HBoolAssign.
Qed.

Theorem OTP2bit_Input_Indep (x1 x2 y1 y2 : bool) :
  hoare_derivable {{ (prob true) = 1 }} OneTimePad_2bit
    {{ (prob ((c1 <-> x1) /\ (c2 <-> x2) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob ((c1 <-> x1) /\ (c2 <-> x2))) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}.
Proof.
  unfold OneTimePad_2bit.
  apply HSeq with (eta2 :=
    {{ (prob ((c1 <-> x1) /\ (m1 <-> y1) /\ (m2 <-> y2)))
       = (prob (c1 <-> x1)) * (prob ((m1 <-> y1) /\ (m2 <-> y2))) }}).
  - apply first_bit.
  - apply second_bit.
Qed.

End OneTimePad.
