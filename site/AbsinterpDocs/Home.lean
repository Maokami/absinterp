import VersoManual

open Verso.Genre Manual

#doc (Manual) "Home" =>
%%%
tag := "home"
%%%

`absinterp` builds reusable abstract-interpretation theory and infrastructure
in Lean 4. The project is organized in layers — a minimal semantic kernel
(`ConcretizationDomain`), a capability layer for reusable domain operations,
generic soundness/iteration/fixpoint scaffolding, CSLib-style LTS adapters,
and an IMP validation layer on top.

# Status

- Soundness-first: every abstract operation is paired with a
  concretization-level soundness proof. `Tests/Axioms.lean` pins the axiom
  footprint of the upstream-candidate path to the standard three
  (`propext`, `Quot.sound`, `Classical.choice`).
- Two independent end-to-end paths are exercised: labeled trace soundness
  (`soundStep_imp` → `soundTraceLifted`) and unlabeled collecting/fixpoint
  soundness (`soundAny_imp` → `omegaReachableLTS_subset_of_isPostFixpoint`).
- Sign, Parity, and Interval scalar domains are packaged with the full
  capability set (bottom, point abstraction, transfers, filters, meet-like,
  relational backward operators).
- The flagship case study `Examples/IMP/Programs/CollectingShowcase.lean`
  proves a real value invariant (`x0 = 5` at the while head of
  `x0 := 5;; while x0 do x0 := x0 + 0`) via the generic IMP collecting
  bridge. The proof is axiom-clean — no `native_decide`.

# Why Lean 4 + abstract interpretation?

Abstract interpretation is a mature semantic framework for building sound
static analyses. Mechanising it in Lean 4 benefits from:

- *Pay-as-you-go algebraic structure.* Only `ConcretizationDomain` +
  `gamma_monotone` + `SemilatticeSup` are needed for join soundness;
  nothing forces a full Galois connection.
- *Typeclass-driven capabilities.* Filters, backward operators, and
  transfers are opt-in structures, each carrying their own soundness
  obligation.
- *CSLib-style LTS semantics.* Aligning the concrete side with CSLib's
  `LTS` / `MTr` / `ωTr` / `HasTau` gives a common vocabulary for future
  upstream packaging and for analyses over other CSLib-defined languages.
- *Axiom hygiene.* `#guard_msgs in #print axioms` makes the
  upstream-candidate path's axiom footprint a compile-time invariant.

# Where to go next

- {ref "architecture"}[Architecture] — the layered design, interface
  choices, and the upstream boundary.
- {ref "reading-guide"}[Reading Guide] — a compact path through the source
  tree and the session-by-session evolution.
- {ref "imp-collecting-showcase"}[IMP Collecting Showcase] — the flagship
  Interval value-invariant theorem and its proof structure.

# Repository

The source, issue tracker, and PRs live at
[github.com/Maokami/absinterp](https://github.com/Maokami/absinterp).
The root `README.md` and `docs/architecture.md` carry deeper detail; this
site restates the same story in a form more suitable for web browsing and
talks.
