# TPHL: A Complete Truth-functional Probabilistic Hoare Logic (Rocq formalization)

This repository contains the Rocq formalization accompanying the paper
*A Complete Truth-functional Probabilistic Hoare Logic*: the logic and its
semantics, soundness, completeness over finite domains, and the example
programs.

## Contents

Everything is in `TPHL/`.

| Path | Contents |
|---|---|
| `PHL.v` | Syntax of programs and assertions, the kernel semantics, validity, and the proof system `hoare_derivable` |
| `AnalysisPrelude.v`, `MeasureIntegration.v`, `CoinLaw.v` | Measure-theoretic preliminaries used by the semantics |
| `Soundness/` | Soundness of every rule; main theorem `hoare_derivable_sound` (`Soundness/HoareSoundness.v`) |
| `Completeness/` | Completeness over finite domains; main theorems `hoare_complete` and `hoare_valid_iff_derivable` (`Completeness/FiniteCompleteness.v`) |
| `SemanticsEquivalence.v` | The paper's measure-transformer semantics agrees with the kernel semantics (`paper_semantics_equiv`, `paper_hoare_valid_iff`) |
| `Examples/` | Example programs verified with the proof system; `Lib.v`, `PrAtoms.v`, `KRoll.v` and `SamplerSpec.v` are shared helpers |

## Requirements

- Rocq 9.0.0
- MathComp 2.6.0
- MathComp-Analysis 1.18.0 (with `rocq-mathcomp-reals-stdlib` and
  `rocq-mathcomp-analysis-stdlib`)
- Hierarchy Builder 1.10.3

`TPHL/toolchain.export` lists the exact opam package set used for testing.

## Building

### Option 1: a dedicated opam switch (exact versions)

From `TPHL/`:

```sh
opam switch create "$PWD/.toolchain" --empty
opam switch import toolchain.export --switch "$PWD/.toolchain"
./build.sh
```

`build.sh` compiles every file listed in `_CoqProject`, in order, with the
switch in `TPHL/.toolchain` (set `TPHL_SWITCH=/path/to/switch` to use another
switch). To compile selected files, pass them as arguments, e.g.
`./build.sh PHL.v Soundness/HoareSoundness.v`.

### Option 2: an existing Rocq installation

With the requirements above installed (for example via
`opam install rocq-core.9.0.0 rocq-mathcomp-analysis.1.18.0
rocq-mathcomp-analysis-stdlib.1.18.0 rocq-mathcomp-reals-stdlib.1.18.0`,
with the `coq-released` opam repository added), from `TPHL/`:

```sh
rocq makefile -f _CoqProject -o Makefile
make
```

A full build takes about 15 minutes on a recent laptop.

## Checking the results

Every file compiles with no `Admitted`, `admit`, `Axiom`, `Parameter` or
`Conjecture`. To list the axioms a result depends on, add for example

```coq
Print Assumptions hoare_derivable_sound.
Print Assumptions hoare_complete.
```

at the end of the corresponding file. The only axioms are the standard
classical, extensionality and choice axioms used by Rocq's real numbers and
MathComp.
