# Handoff: Equivalence of the paper and Rocq semantics

**Status:** proof sketch only (not formalized yet). Branch: `semantics`.

**Goal.** Show that the denotational semantics of pWHILE in the paper
*A Complete Truth-functional Probabilistic Hoare Logic* (Fig. 4, App. A.1)
coincides with the kernel semantics in `TPHL/PHL.v` (`CommandSemantics.denote`,
`transform_cmd`).

## Setup

- 𝒱: valuations, with the discrete σ-algebra. G: sub-probability measures on 𝒱.
- **Paper semantics** 𝒫⟦s⟧ : G → G, as in Fig. 4.
- **Code semantics** 𝒦⟦s⟧ : 𝒱 → G is the kernel `denote s`. It induces
  T_k(μ)(A) := ∫ k(v)(A) dμ(v)  (`transform`).
- Restriction: μ_β(A) := μ(A ∩ ⟦β⟧).

**Theorem.** If every toss rate in s lies in [0,1], then for all μ ∈ G and all A ⊆ 𝒱,

    𝒫⟦s⟧(μ)(A) = T_{𝒦⟦s⟧}(μ)(A).

Proof by structural induction on s, with the hypothesis quantified over **all**
μ ∈ G (the `if` and `while` cases use it at restrictions and iterates of μ).
G is closed under restriction and under every T_k (`transform_subprob`).

## General facts about T

| | Statement | Rocq |
|---|---|---|
| F1 | Deterministic kernels: T_{δ∘f}(μ)(A) = μ(f⁻¹A) | `transform_deterministic` |
| F2 | Composition: T_{seq k l} = T_l ∘ T_k | `transform_sequence` (via `integral_kcomp`) |
| F3 | Branching: T_{branch β k l}(μ) = T_k(μ_β) + T_l(μ_¬β) | `transform_branch` |
| F4 | Series: T_{Σₙkₙ}(μ)(A) = Σₙ T_{kₙ}(μ)(A) (monotone convergence) | **missing** |
| F5 | Zero kernel: T_0(μ) = 0 | follows from `kzero` |

All existing lemmas are in `TPHL/Soundness/CommandFacts.v`.

## Cases

**skip, assignments.** By F1 with f = id or f = δᵉₘ, giving μ ∘ (δᵉₘ)⁻¹ as in Fig. 4.
Side condition: `cformula_eval_bool β v = true` iff v ⊩c β.

**toss(b, r), r ∈ [0,1].** By `toss_event_valid`,
𝒦(v)(A) = r·1_A(v[b↦tt]) + (1−r)·1_A(v[b↦ff]). Integrating over μ and using
linearity gives r·𝒫⟦b←tt⟧μ(A) + (1−r)·𝒫⟦b←ff⟧μ(A).
If r ∉ [0,1], the code gives 0 (`toss_invalid`) and the paper's semantics is
undefined, hence the well-formedness hypothesis.

**s₁; s₂.** By F2 and the inductive hypothesis at μ and at 𝒫⟦s₁⟧μ ∈ G.

**if β then s₁ else s₂.** By F3 and the inductive hypothesis at μ_β and μ_¬β.

**while β do s.** Let k = 𝒦⟦s⟧, Eₙ = `loop_exit β k n`, and F(μ) := 𝒫⟦s⟧(μ_β).
Then the paper's iterates are μⁱ = Fⁱ(μ), so 𝒫⟦while⟧(μ) = Σᵢ (Fⁱμ)_¬β.
By the inductive hypothesis, F(μ) = T_k(μ_β) on G, and G is closed under F.

*Key lemma (unrolling).* For all n and all μ ∈ G: T_{Eₙ}(μ) = (Fⁿμ)_¬β.

The code peels off the *first* iteration (Eₙ₊₁ = body; Eₙ), while the paper
builds up from the *last* (μⁿ = F(μⁿ⁻¹)). The induction on n must therefore
generalize over μ.

- n = 0: E₀ = branch β 0 skip, so T_{E₀}(μ) = 0 + μ_¬β (F3, F5, F1).
- n + 1: Eₙ₊₁ = branch β (seq k Eₙ) 0, so
  T_{Eₙ₊₁}(μ) = T_{seq k Eₙ}(μ_β)   (F3, F5)
             = T_{Eₙ}(T_k(μ_β))      (F2)
             = T_{Eₙ}(Fμ)            (IH for s)
             = (Fⁿ(Fμ))_¬β           (IH for n at Fμ ∈ G)
             = (Fⁿ⁺¹μ)_¬β.

*Conclusion.* `loop β k` = Σₙ Eₙ (`kseries`, `loop_event`), so by F4 and the key
lemma, T_{loop}(μ)(A) = Σₙ (Fⁿμ)_¬β(A) = 𝒫⟦while⟧(μ)(A). ∎

## Formalization plan (e.g. new `TPHL/Equivalence.v`)

1. Define `pdenote : Cmd D -> carrier -> carrier` directly from Fig. 4:
   pushforward, scaled sums, restriction, and a measure series for `while`.
   Showing the series stays in G is Prop. A.1 (reuse, or get it from the theorem).
2. Define `toss_rates_valid c`: every toss rate in `c` lies in [0,1].
3. New lemmas: `transform_series` (F4); `transform_toss` (from
   `toss_event_valid`, `integral_indic`, linearity); the unrolling lemma.
4. Main theorem, by induction on `c` with μ generalized:
   `pdenote_transform : toss_rates_valid c -> Subprob mu -> pdenote c mu A = transform_cmd c mu A`.

The likely hardest part is F4 and the measure-series bookkeeping, not the
semantic argument.

## Related notes

- Code comments in `TPHL/PHL.v` and `TPHL/Soundness/CommandFacts.v` cite
  "Def. 5" and "Prop. 12". In the current paper draft these are Def. 4.1 and
  Prop. A.1. Worth updating.
- The code allows any real toss rate (out-of-range rates denote the zero
  kernel, as in CPHL). The paper restricts r to [0,1] ∩ dR.
