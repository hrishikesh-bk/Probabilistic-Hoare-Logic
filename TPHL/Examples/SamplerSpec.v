(** Specification of the sampler used by the escaping spline.

    [sampler_spec S] says that, started
    with all mass on [x = k], the command [S] sets [val] to 0 with probability
    [1/(k+1)], to a non-zero value with probability [1 - 1/(k+1)], and leaves
    [x = k] with all the mass.  [UniformX.v] proves it for a concrete sampler
    built from fair coins. *)
From Stdlib Require Import Reals Lra Strings.String.
Require Import PHL Examples.Lib.

Open Scope R_scope.
Open Scope string_scope.
Open Scope tphl_scope.

Module SamplerSpec.

Notation x := (dom_program_var "x").
Notation val := (dom_program_var "val").

Definition sampler_pre (k : nat) : PFormula :=
  {{ (prob (x = k)) = 1 /\ (prob (x = k)) = (prob true) }}.

Record sampler_spec (S : Cmd) : Prop := {
  spec_zero : forall k : nat,
    hoare_derivable (sampler_pre k) S
      (p_eq (PProb \{ x = k /\ val = #(0%nat) \}) (PConst (1 / (INR k + 1))));
  spec_nonzero : forall k : nat,
    hoare_derivable (sampler_pre k) S
      (p_eq (PProb \{ x = k /\ ~ (val = #(0%nat)) \}) (PConst (1 - 1 / (INR k + 1))));
  spec_xinv : forall k : nat,
    hoare_derivable (sampler_pre k) S {{ (prob (x = k)) = (prob true) }}
}.

End SamplerSpec.
