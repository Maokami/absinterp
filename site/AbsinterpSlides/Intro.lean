import VersoManual

open Verso.Genre Manual

/-!
A minimal talk deck for `absinterp`. Built with `VersoManual` because the
official Verso stack does not yet ship a dedicated slide genre; each
top-level section is a logical slide. The executable emits a single-file
HTML that can be opened in a browser and scrolled through, or styled
downstream for slide-show rendering. Replace with the official Verso
slide genre once it ships a tag compatible with the repository toolchain.
-/

#doc (Manual) "Layered Abstract Interpretation in Lean 4" =>
%%%
shortTitle := "absinterp slides"
authors := ["absinterp contributors"]
%%%

A short talk deck for `absinterp`.

# Project goal

`absinterp` is a Lean 4 library for *reusable* abstract interpretation
over *CSLib-style LTS semantics*. IMP is the validation case study,
not the product.

- Soundness-first, γ-only — no Galois connection required.
- Long-term target: mature the reusable pieces toward an upstream CSLib
  contribution.

# Layered architecture

The framework is a strict, one-directional stack.

- *Semantic core.* `Concretization`, `ConcretizationDomain`,
  `gamma_union_subset_sup`.
- *Domain capabilities.* `BottomConcretization`, `MeetLike`,
  `PointAbstraction`, `FilterOperator`, `RelationalBackwardOperator`,
  transfers.
- *Generic soundness + iteration.* Step/trace lifting, collecting
  semantics, the fixpoint bridge, the widening engine.
- *CSLib LTS adapters.* `LTSAbstraction` (trace) and
  `LTSCollectingAbstraction` (collecting).
- *IMP adapter.* `IMPAnalysisDomain`, `transferProgram`,
  `transferAnyProgram`, per-domain wrappers, programs.

Higher layers depend only on lower layers. IMP arithmetic never leaks
into the framework core.

# Trace vs. collecting paths

The framework ships two independent end-to-end paths.

: Labeled trace path

  `LTSAbstraction` takes a labeled `Label → Abstract → Abstract`
  transfer plus a step-soundness proof; `soundTraceLifted` derives
  trace-level soundness.

: Unlabeled collecting/fixpoint path

  `LTSCollectingAbstraction` takes an unlabeled `Abstract → Abstract`
  transfer plus `postAny`-soundness; the fixpoint bridge
  `omegaReachable_subset_of_isPostFixpoint` turns an abstract
  post-fixpoint into a concrete safety conclusion.

The two paths are kept parallel on purpose: bridging them requires
extra structure (finite label enumeration, abstract aggregation) that
only some clients can pay for.

# IMP case studies

IMP exercises the framework end-to-end.

- *`Programs/Showcase.lean`* — labeled Sign analysis along fixed
  traces over the canonical IMP LTS.
- *`Programs/WidenShowcase.lean`* — widening on a small finite
  `Flat3` domain, exercising `WAcc` / `witer` / `pfp`.
- *`Programs/CollectingShowcase.lean`* — the flagship collecting
  case study: proves `x0 = 5` at the while head of
  `x0 := 5;; while x0 do x0 := x0 + 0` via a hand-written Interval
  post-fixpoint. Axiom-clean — no `native_decide`.

# Upstream boundary

Candidates for CSLib upstreaming:

- semantic kernel (`ConcretizationDomain`, `gamma_union_subset_sup`);
- capability layer;
- generic soundness + iteration + fixpoint + widening;
- CSLib LTS adapters (`LTSAbstraction`, `LTSCollectingAbstraction`,
  readout helpers).

Lives only in this repo:

- IMP syntax/semantics/`impLTS`;
- `IMPAnalysisDomain`;
- program-specific showcases and tutorials.

The split is principled: anything mentioning IMP belongs above the
framework boundary.

# Status and next steps

- Axiom-clean upstream-candidate path, with `Tests/Axioms.lean` as
  a compile-time guard on the axiom footprint.
- Two flagship showcase invariants in place (Sign trace, Interval
  collecting `x0 = 5`).
- Still open: relational domain instances, narrowing, realistic
  widening over config abstractions, namespacing/docstring pass for
  the first CSLib PR.

# Pointers

- Repository:
  [github.com/Maokami/absinterp](https://github.com/Maokami/absinterp)
- Architecture note: `docs/architecture.md`
- Documentation site: this Verso project
