(** Completeness of TPHL over finite domains (Theorem 11).

    By induction on the program, every command over a finite domain has a
    certificate (Lemma 25): atomic commands directly, sequencing and
    conditionals by composition, and loops by LoopCertificate.v, whose body
    triples use completeness for the loop body.  A certificate yields
    weakest preconditions, so every valid triple is derivable
    (Corollary 26). *)
From Stdlib Require Import Reals.
Require Import PHL Soundness.HoareSoundness.
Require Import Completeness.Interface Completeness.WeakestPrecondition
  Completeness.AtomicCertificates Completeness.CompositeCertificates
  Completeness.FiniteDomain Completeness.LoopCertificate.

Section FiniteCompleteness.
Context {D : Domain} (FD : FiniteDomain D).

Theorem certificate_exists (c : Cmd D) : exists T, certificate c T.
Proof.
  induction c as [|x t|b beta|b r|c1 [T1 H1] c2 [T2 H2]|beta c1 [T1 H1] c2 [T2 H2]|beta body [T HT]].
  - exists skip_transformer. apply skip_certificate.
  - exists (dom_assign_transformer x t). apply dom_assign_certificate.
  - exists (bool_assign_transformer b beta). apply bool_assign_certificate.
  - exists (toss_transformer b r). apply toss_certificate.
  - exists (seq_transformer c1 T1 T2). apply seq_certificate; assumption.
  - exists (if_transformer beta T1 T2). apply if_certificate; assumption.
  - exists (loop_transformer FD beta body). apply loop_certificate.
    intros pre post Hv. exact (certified_relative_complete body T HT pre post Hv).
Qed.

(** Theorem 11: over a finite domain, every valid triple is derivable. *)
Theorem hoare_complete (pre : PFormula D) (c : Cmd D) (post : PFormula D) :
  hoare_valid pre c post -> hoare_derivable pre c post.
Proof.
  intros Hv. destruct (certificate_exists c) as [T HT].
  exact (certified_relative_complete c T HT pre post Hv).
Qed.

(** Soundness and completeness together. *)
Corollary hoare_valid_iff_derivable (pre : PFormula D) (c : Cmd D) (post : PFormula D) :
  hoare_valid pre c post <-> hoare_derivable pre c post.
Proof.
  split; [apply hoare_complete | apply hoare_derivable_sound].
Qed.

End FiniteCompleteness.

(** A concrete finite domain, so that the hypothesis is satisfiable: Booleans
    with exclusive-or and equality. *)
Inductive BoolOp : Type := BXor.
Inductive BoolRel : Type := BEq.

Definition bool_domain : Domain :=
  {| dom_carrier := bool;
     dom_eq_dec := Bool.bool_dec;
     dom_op := BoolOp;
     dom_op_eval := fun _ => xorb;
     dom_rel := BoolRel;
     dom_rel_eval := fun _ => Bool.eqb |}.

Definition bool_finite : FiniteDomain.FiniteDomain bool_domain.
Proof.
  refine (@FiniteDomain.Build_FiniteDomain bool_domain
            (true :: false :: nil)%list _ BEq _ true).
  - intros []; cbn; auto.
  - intros a b. cbn. split; [apply Bool.eqb_prop | intros ->; apply Bool.eqb_reflx].
Defined.

Example bool_domain_complete (pre post : PFormula bool_domain) (c : Cmd bool_domain) :
  hoare_valid pre c post <-> hoare_derivable pre c post :=
  hoare_valid_iff_derivable bool_finite pre c post.
