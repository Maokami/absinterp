import VersoManual

open Verso.Genre Manual

/-!
Research-seminar deck for `absinterp` — targeted at a 20–30 minute
technical talk to Lean users and PL / static-analysis researchers.

Kept in the same library as the short overview deck
(`AbsinterpSlides.Intro`), but exposed through a dedicated executable
(`seminar-slides`) so it can publish to its own URL. Rendering is
`VersoManual`-based, matching the rest of the docs project; migrate
when Verso ships a toolchain-compatible slide genre.
-/

#doc (Manual) "Layered Abstract Interpretation in Lean 4 — seminar edition" =>
%%%
shortTitle := "absinterp seminar"
authors := ["Maokami"]
%%%

A 20–30 minute seminar on `absinterp` — a reusable Lean 4
abstract-interpretation framework over CSLib-style LTS semantics,
validated on IMP with an axiom-clean value invariant.

This deck explains *why* the architecture looks the way it does, not
just *what* it contains. It is deeper and slower than the short
overview deck at `/slides/`.

# Motivation: the gap

Abstract interpretation is mature theory (Cousot–Cousot 1977, widening
and narrowing, γ-only formulations). The Lean 4 ecosystem already
ships the concrete-side machinery it needs:

- CSLib — `LTS`, `MTr`, `ωTr`, `HasTau`, divergence, ω-execution.
- Mathlib — `SemilatticeSup`, `OrderTop`, lattice instances, `Pi`
  constructions.
- Lean 4 — `#print axioms`, `#guard_msgs`, axiom-hygiene at compile
  time.

What is *missing* is a reusable, mechanized, γ-only abstract
interpretation layer that sits on top of those primitives and is
designed to go into CSLib, not into one paper.

# The research question

> What is the smallest reusable mechanized kernel for abstract
> interpretation in Lean 4 over CSLib-style LTS semantics, and how do
> we keep it from collapsing into a language-specific analyzer?

Three sub-questions shape the design:

- Can the kernel avoid a mandatory Galois connection?
- Can scalar-domain operations be *pay-as-you-go* rather than forced by
  the core interface?
- Can labeled trace soundness and unlabeled collecting/fixpoint
  soundness share a foundation without coupling into each other?

# Design constraints

Five constraints drive the entire framework shape:

- *Soundness first.* Every abstract operation is paired with a
  concretization-level proof obligation.
- *γ-only.* No α, no Galois-connection obligation in the core.
- *Axiom-clean upstream path.* Only `propext`, `Quot.sound`,
  `Classical.choice` on the candidate-upstream surface; pinned by
  `Tests/Axioms.lean`.
- *Strict one-directional layering.* Framework cannot reach into
  language adapters. IMP arithmetic never leaks upward.
- *CSLib-native.* The concrete side is an `LTS`, not a
  re-implementation.

# Architecture: the stack

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

One-directional: each layer consumes only lower layers.
Nothing in layers 1–4 mentions IMP.

# Architecture: what lives where

- *1 Semantic core* — the minimum required for soundness:
  `Concretization`, `ConcretizationDomain` (γ + monotonicity + top),
  `gamma_union_subset_sup`.
- *2 Domain capabilities* — opt-in operations: `BottomConcretization`,
  `MeetLike`, `FilterOperator`, `RelationalBackwardOperator`,
  `UnaryTransfer`, `BinaryTransfer`.
- *3 Generic soundness + iteration* — `soundTrace_of_soundStep`,
  collecting semantics, `IsPostFixpoint` bridge, widening engine.
- *4 CSLib LTS adapters* — `LTSAbstraction` (labeled),
  `LTSCollectingAbstraction` (unlabeled), readout helpers.
- *5 IMP adapters + case studies* — `IMPAnalysisDomain`,
  per-domain wrappers, programs.

# Interface design I: minimal kernel

`ConcretizationDomain` is deliberately *tiny*.

```
structure ConcretizationDomain
    (Abstract : Type u) [Preorder Abstract] [OrderTop Abstract]
    (Concrete : Type v) where
  gamma          : Concretization Abstract Concrete
  gamma_monotone : ∀ ⦃a b⦄, a ≤ b → gamma a ⊆ gamma b
  gamma_top      : ∀ c, c ∈ gamma ⊤
```

- Join soundness is a *theorem* (`gamma_union_subset_sup`), not a
  field. Proof: `gamma_monotone` + `SemilatticeSup`.
- An earlier iteration stored `join_sound`; removing it eliminated
  duplication and aligned with Mathlib's instance resolution.
- Bottom soundness is a *capability*, not a kernel field — some
  domains don't have a cleanly-empty ⊥.

# Interface design II: capabilities, not a big lattice

Operations above the kernel are packaged as *capabilities*, each
bundling a function with its soundness (and sometimes reductiveness)
proof.

Why capabilities, not a monolithic full-lattice domain?

- Not every domain has a lattice `Inf` that agrees with what analyses
  actually want (e.g. `intersectParity` disagrees with the lattice
  infimum).
- `FilterOperator` / `RelationalBackwardOperator` make sense only for
  languages whose conditions and operators match them; forcing them
  into the core would fake them for everyone.
- The capability style lets a client pay only for the operations it
  genuinely needs.

# Trace path

The labeled path mechanizes *one-step soundness → trace soundness*.

- `LTSAbstraction` packages a CSLib `LTS` with a labeled transfer
  `Label → Abstract → Abstract` and a step-soundness proof
  `SoundStep (postStep lts) γ transfer`.
- `soundTrace_of_soundStep` lifts that to `SoundTrace` over
  `liftTracePost`.
- `LTSAbstraction.soundTraceLifted` is the derived public theorem.

The abstraction boundary that makes this reusable: *the framework
does not see how the transfer is computed — only that it is
step-sound*.

# Collecting / fixpoint path

The unlabeled path mechanizes *post-fixpoint → ω-reachability*.

- `LTSCollectingAbstraction` packages a CSLib `LTS` with an unlabeled
  transfer `Abstract → Abstract` and a `postAny`-soundness proof.
- Reach transfer: `initAbs ⊔ transferAny ·`.
- `IsPostFixpoint` is the fixpoint vocabulary.
- Bridge: `omegaReachable_subset_of_isPostFixpoint` — an abstract
  post-fixpoint `a` implies `omegaReachableLTS init ⊆ γ a`.

The abstraction boundary: *an abstract solver hands back a
post-fixpoint; the framework hands back a concrete safety
statement*.

# Why parallel, not unified

Both paths target soundness of an abstract transfer, so why not one
interface?

- A labeled transfer `Label → Abstract → Abstract` carries *strictly
  more information* than an unlabeled one.
- Deriving the unlabeled version requires extra structure:
  either *finite label enumeration* or *abstract aggregation over
  labels*.
- Neither is free. Finite labels rule out real languages;
  aggregation forces join costs on every label even when the client
  doesn't need them.

We keep two lanes. Clients pay for the one they actually use.

# Flagship: program and theorem

```
x0 := 5 ;;
while x0 do
  x0 := x0 + 0
```

```
theorem x0_eq_5_at_wloop (σ : Store)
    (hOmega : (wloop, σ) ∈ omegaReachableLTS impLTS init) :
    σ Var.x0 = 5
```

This is the headline result of the collecting path. It asserts a real
*value* invariant — not `ActiveIn`, not a sign-domain
approximation — about an actually-divergent program.

# Flagship: proof shape

A hand-written abstract post-fixpoint
`fix : ConfigSharp Interval`:

- `x0 = [5, 5]` at the three loop-related active controls
  (`.seq .skip wloop`, `wloop`, `.seq body wloop`);
- `⊤` at every other (control, variable) pair.

Three obligations, each small:

1. `init ⊆ gammaProgramInterval program fix` — trivial at the program
   entry (`fix = ⊤` there).
2. `IsPostFixpoint (· ≤ ·) (impIntervalReachTransfer program fix) fix`
   — discharged pointwise. The three non-trivial cases reduce by
   structural unfolding + `Pi.sup_apply` to `mk 5 5 = mk 5 5`.
3. Apply `omegaReachableLTS_subset_of_isPostFixpoint_impInterval` and
   extract `σ Var.x0 ∈ gammaInterval (mk 5 5) = {5}`; finish with
   `omega`.

*Axiom-clean* — `propext`, `Quot.sound`, `Classical.choice` only;
no `native_decide`.

# Design tradeoffs / rejected alternatives

: Galois connections in the core

  *Rejected.* Many useful domains do not have a clean `α`. γ-only is
  sufficient for soundness. Keeping `α` opt-in — a separate
  `GaloisConnection` bridge — preserves the kernel's minimality.

: Unified labeled / unlabeled interface

  *Rejected.* Bridging costs finite label enumeration or abstract
  aggregation. Keeping the lanes parallel lets each client pay only
  for what it uses.

: `gammaProgram` as a literal `ConcretizationDomain`

  *Rejected.* IMP's γ carries an `ActiveIn program` constraint that
  violates `gamma_top` for arbitrary configurations. IMP ships
  specialised bridge theorems instead of a literal
  `LTSCollectingAbstraction` value.

: `IMPAnalysisDomain` in the framework core

  *Rejected.* The interface is arithmetic-specific and only makes
  sense for an IMP-shaped language. Lifting it would break the
  language-agnostic story.

# Upstream boundary

*CSLib upstream candidates:*

- Layer 1 — `Concretization`, `ConcretizationDomain`,
  `gamma_union_subset_sup`.
- Layer 2 — capability layer.
- Layer 3 — generic soundness (`Sound`, `SoundStep`, `SoundTrace`,
  `soundTrace_of_soundStep`), iteration (`iterateNat`,
  `CollectingStep`, `reachF`, `kleeneNat`,
  `omegaReachable_subset_iUnion_kleeneNat`), fixpoint/widening
  (`IsPostFixpoint`, `*_subset_of_isPostFixpoint`, `WAcc`, `witer`,
  `pfp`).
- Layer 4 — `LTSAbstraction`, `LTSCollectingAbstraction`,
  `StepSoundOfRead`, `CollectingSoundOfRead`.

*Stays local:*

- Layer 5 — IMP syntax, semantics, `impLTS`, `IMPAnalysisDomain`,
  per-domain wrappers, programs, tutorials.

A first CSLib PR would lift Layer 1 and a selected subset of Layer 2.

# Limitations and future work

- *Scalar domains only.* Sign, Parity, Interval are in place.
  Relational domains (congruences, pairwise difference) are natural
  next targets and will stress-test the kernel's minimality.
- *Widening is wired only on toy flat lattices.* Realistic
  widening over `ConfigSharp` (program-relative config abstractions)
  is open.
- *Narrowing is not packaged* as a reusable combinator.
- *Weak / τ path* exists but has not been exercised end-to-end at the
  collecting/omega layer.
- *Upstream packaging* — namespaces and docstrings still need a
  sweep before the first CSLib PR.
- *Slide-genre migration* — the decks will move to an official Verso
  slide genre when one ships with a matching toolchain tag.

# Summary

- A minimal γ-only kernel (`ConcretizationDomain`) is enough for a
  reusable mechanized AI layer in Lean 4.
- Labeled trace and unlabeled collecting/fixpoint paths coexist
  because merging them would impose costs not every client can pay.
- IMP is a validator, not the product; nothing below Layer 5 mentions
  it.
- The `x0 = 5` case study shows the framework delivers genuine
  value invariants, axiom-clean, through the generic collecting
  bridge.
- The bottom layers are ready to be considered for a first CSLib PR.

# Appendix A · proof skeleton of `x0 = 5`

```
theorem x0_eq_5_at_wloop (σ : Store)
    (hOmega : (wloop, σ) ∈ omegaReachableLTS impLTS init) :
    σ Var.x0 = 5 := by
  have hGamma : (wloop, σ) ∈ gammaProgramInterval program fix :=
    omegaReachableLTS_subset_of_isPostFixpoint_impInterval
      program init fix fix init_subset_gamma fix_isPostFixpoint hOmega
  have hx0 : σ Var.x0 ∈ gammaInterval (fix wloop Var.x0) :=
    hGamma.2 Var.x0
  rw [fix_C_x0] at hx0
  have := (mem_gammaInterval_mk_iff 5 5 (σ Var.x0)).mp hx0
  omega
```

Three supporting lemmas compute `transferAnyProgram … fix` at the
three loop-related active controls; each finishes with `rfl` after
structural unfolding.

# Appendix B · explicit upstream candidates

*Top priority* for a first CSLib PR:

- `AbsInterp.Framework.Concretization`
- `AbsInterp.Framework.Domains.Concretization`
  (`ConcretizationDomain`, `gamma_union_subset_sup`)

*Next wave*:

- `AbsInterp.Framework.Domains.Capabilities.*`
- `AbsInterp.Framework.Soundness.*`
- `AbsInterp.Framework.Iteration.NatIter`
- `AbsInterp.Framework.Iteration.Collecting`
- `AbsInterp.Framework.Iteration.Fixpoint.*`

*Adapter wave* (after semantic-kernel upstreaming settles):

- `AbsInterp.Instances.LTS.Semantics.*`
- `AbsInterp.Instances.LTS.Instantiation.{Interface,Soundness,CollectingInterface,CollectingSoundness}`
- `AbsInterp.Instances.LTS.Analyses.Common`

# Appendix C · orientation

```
AbsInterp/
  Framework/              -- Layers 1–3
    Concretization.lean
    Domains/
    Soundness/
    Iteration/
      NatIter.lean
      Collecting.lean
      Fixpoint/
      Widening/
  Instances/LTS/          -- Layer 4
    Semantics/
    Instantiation/
    Analyses/Common.lean
  Domains/                -- Sign, Parity, Interval
Examples/IMP/             -- Layer 5
  Analysis/Generic/{Defs,Lemmas,Soundness,Collecting}.lean
  Analysis/{Sign,Interval,Parity}/Defs.lean
  Programs/{Showcase,CollectingShowcase,WidenShowcase}.lean
Tests/
  Axioms.lean
```
