import VersoManual

open Verso.Genre Manual

/-!
Talk deck for `absinterp`. Built with `VersoManual` because the
repository's pinned Verso/toolchain combination does not ship a
dedicated slide genre; each top-level `#` section is one logical slide
(about one minute of delivery). When Verso ships an official slide
genre with a matching toolchain tag, migrate this module to it.
-/

#doc (Manual) "Layered Abstract Interpretation in Lean 4" =>
%%%
shortTitle := "absinterp slides"
authors := ["Maokami"]
%%%

A 10–15 minute talk on `absinterp` — a reusable Lean 4
abstract-interpretation framework built over CSLib-style LTS
semantics, validated on IMP with an axiom-clean value invariant.

# The problem

Abstract interpretation is mature theory.
Lean 4 + CSLib already ship the concrete-side primitives —
`LTS`, `MTr`, `ωTr`, `HasTau`.

What is missing: a *reusable, γ-only* abstract-interpretation layer
sitting cleanly on top.

`absinterp` builds that layer.

- Soundness-first. Every abstract operation comes with a
  concretization-level proof.
- γ-only. No Galois connection required.
- CSLib-native. The concrete side is an LTS, not a re-implementation.

# Not an IMP analyzer

*Before:* one-off analyzers per language, reproving the same
boilerplate — monotone lifts, trace lifting, fixpoint soundness.

*After:* a small layered stack. IMP is the *first validator*, not the
product.

- No `IMP` identifier ever appears in the framework core.
- Adding a new language means instantiating an adapter, not rebuilding
  the theory.
- Everything below the adapter layer is language- and domain-agnostic.

# Layered architecture

```
┌────────────────────────────────────────┐
│ 5 · IMP adapters + case studies        │
├────────────────────────────────────────┤
│ 4 · CSLib LTS adapters                 │
├────────────────────────────────────────┤
│ 3 · Generic soundness + iteration      │
├────────────────────────────────────────┤
│ 2 · Domain capabilities                │
├────────────────────────────────────────┤
│ 1 · Semantic core                      │
└────────────────────────────────────────┘
```

- *5* — `IMPAnalysisDomain`, per-domain wrappers, showcases.
- *4* — `LTSAbstraction` (trace) · `LTSCollectingAbstraction` (collecting).
- *3* — trace lifting, fixpoint bridge, widening engine.
- *2* — filters, meet-like, backward operators, transfers.
- *1* — `ConcretizationDomain` + `gamma_union_subset_sup`.

Strict, one-directional: every layer depends only on lower layers.

# Two paths out of the framework

: Labeled trace path

  `LTSAbstraction` takes a labeled transfer
  `Label → Abstract → Abstract` and a one-step soundness proof.
  `soundTraceLifted` derives `SoundTrace` over `liftTracePost`.

: Unlabeled collecting / fixpoint path

  `LTSCollectingAbstraction` takes an unlabeled transfer
  `Abstract → Abstract` and a `postAny`-soundness proof.
  `omegaReachable_subset_of_isPostFixpoint` turns an abstract
  post-fixpoint into `omegaReachableLTS init ⊆ γ a`.

Why parallel, not unified? Bridging them costs finite label
enumeration or abstract aggregation — a price only *some* clients can
pay.

# Flagship: `x0 = 5` through the collecting bridge

```
x0 := 5 ;;
while x0 do
  x0 := x0 + 0
```

*Theorem.* For every `(wloop, σ) ∈ omegaReachableLTS impLTS init`,
`σ Var.x0 = 5`.

Why it matters:

- A real *value* invariant — not `ActiveIn`, not a sign-domain
  approximation.
- Hand-written Interval post-fixpoint `[5, 5]`, closed under every
  transfer the program touches.
- Proof rides the generic collecting bridge end-to-end, not a bespoke
  loop argument.
- *Axiom-clean* — `propext`, `Quot.sound`, `Classical.choice` only;
  no `native_decide`.

# Upstream boundary

*Candidates for CSLib*:

- `Concretization`, `ConcretizationDomain`, `gamma_union_subset_sup`.
- Capability layer — filters, meet-like, backward operators,
  transfers.
- Generic soundness + iteration + fixpoint + widening.
- `LTSAbstraction`, `LTSCollectingAbstraction`, readout helpers.

*Stays local*:

- IMP syntax, semantics, `impLTS`.
- `IMPAnalysisDomain`.
- Program-specific showcases, tutorial LTSs.

The split is principled: anything mentioning IMP stays *above* the
framework boundary.

# Status and what's next

- Axiom footprint pinned at compile time by `Tests/Axioms.lean`.
- Two flagship invariants in place: Sign trace analysis and Interval
  collecting `x0 = 5`.
- Open work:
  - relational domains (congruences, pairwise difference);
  - narrowing and realistic config-level widening;
  - namespacing + docstring sweep for the first CSLib PR;
  - migrate the slide deck to the official Verso slide genre when a
    matching toolchain tag ships.

# Pointers

- Code — [`github.com/Maokami/absinterp`](https://github.com/Maokami/absinterp)
- Live docs — [`maokami.github.io/absinterp/`](https://maokami.github.io/absinterp/)
- Architecture note — `docs/architecture.md` (also in the docs site)
