# Probabilistic-Hoare-Logic

A formalization of logic TPHL from research paper 'A Complete Truth-functional Probabilistic Hoare Logic', along with proofs of example propbabilistic programs as discussed in the paper.

The formalization is implemented in the Rocq theorem prover (tested with Rocq 9.0, MathComp 2.6.0 and MathComp-Analysis 1.18.0). It is in the `TPHL` folder: the logic and its semantics in `TPHL/PHL.v`, soundness in `TPHL/Soundness`, completeness in `TPHL/Completeness`, and the example programs in `TPHL/Examples`.

All examples and the `TPHL` library use the same `_CoqProject` and `Makefile`.
Use a Rocq environment with the project's MathComp, MathComp Analysis, and
Hierarchy Builder dependencies installed. To regenerate the existing build
and compile everything:

```sh
rocq makefile -f _CoqProject -o Makefile
make
```

The project file already lists the sources; do not add `*.v` to the generation
command. To compile selected examples with the same build:

```sh
make TPHL/Examples/BatchTransfer.vo TPHL/Examples/SensorFusion.vo
```

If selecting an existing toolchain explicitly, pass `COQBIN=/path/to/bin/` to
`make`; that selection applies to all targets.

The two new examples use the proof system in `TPHL/PHL.v`:

- `TPHL/Examples/BatchTransfer.v`: `BatchTransfer.batch_transfer` proves exact batch success
  and both receiver-safety assertions over `nat_domain`, for every `K` and `N`.
  `BatchTransferTiming.batch_transfer_fast` proves the fast-path probability
  under `K > 0`. Here `K` counts total attempts. The unqualified fast-path
  claim is false when `K = 0` and `N > 0`.
- `TPHL/Examples/SensorFusion.v`: `SensorFusion.sensor_fusion` proves preservation of
  independence, exact marginals, the alarm rate, and conditional independence
  on the input class `a ∧ b`, over any domain. The proof uses explicit loop
  certificates, SUM and ELIMV to combine input classes, and SEQ, AND and CONS
  to compose the relays. It does not invoke the soundness or completeness
  theorem.



`TPHL/SemanticsEquivalence.v` defines `PaperSemantics.transform_cmd`
independently using pushforwards, restrictions, weighted sums, and the
paper's forward loop recurrence. It uses only the existing dependencies.

- `paper_semantics_equiv` proves equality with the kernel-induced transformer
  on every event for every countably additive sub-probability input measure.
  `paper_semantics_measure_eq` states equality of the measure objects, and
  `paper_semantics_integral` gives the integral formulation.
- `paper_semantics_subprob` and `paper_semantics_mass_nonincrease` establish
  preservation and the output mass bound.
- `paper_psatisfies_equiv`, `paper_hoare_valid_iff`, and
  `paper_hoare_derivable_sound` transfer assertion satisfaction, Hoare validity,
  and the existing calculus's soundness to the independent transformer.

The result uses the existing binary-signature command syntax and imposes no
countability, countable-support, or termination assumption. Invalid toss rates
are extended to zero, matching the kernel semantics; `PaperSemantics.valid_rates`
and the `*_valid_rates` corollaries identify the paper's valid-rate fragment.
This does not formalize EPPL assertion provability or an arbitrary-arity syntax.

References:
Maps.v is taken from the Software Foundations book (https://softwarefoundations.cis.upenn.edu). 
