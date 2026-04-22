import VersoManual

open Verso.Genre Manual

#doc (Manual) "Architecture" =>
%%%
tag := "architecture"
%%%

This chapter adapts `docs/architecture.md` for web browsing. Read the
original alongside the source tree for the fullest picture.

# Goals

Two linked goals drive the project.

- *Build a reusable AI framework in Lean 4.* The target is reusable
  theory and infrastructure — semantic transformers, soundness interfaces,
  iteration scaffolding, and LTS-facing adapters — that another language
  or another abstract domain can plug into without re-proving boilerplate.
  The design is soundness-first.
- *Validate that framework on a non-trivial but manageable language.*
  IMP plays that role. The IMP case study exercises the labeled trace
  path, the unlabeled collecting/fixpoint path, and the widening
  iteration interface.

The project is γ-only: no Galois connection is required. There is no
ambition to ship an industrial IMP analyzer — the value lives in the
reusable layers below `Examples/IMP`.

# Design principles

- *Soundness first.* Every abstract operation carries a
  concretization-level soundness proof. `Tests/Axioms.lean` fixes the
  axiom footprint of the upstream-candidate path at compile time.
- *Keep the semantic kernel small.* `ConcretizationDomain` carries
  only `gamma`, `gamma_monotone`, and `gamma_top`. Anything derivable is
  a theorem, not a stored field.
- *Separate meaning from operations.* `ConcretizationDomain` says
  *what the abstract values mean*. Filters, backward operators, and
  binary transfers are opt-in capabilities above the kernel.
- *Keep framework and adapters structurally separate.*
  `AbsInterp/Framework` cannot import from `Instances/` or `Examples/`.
  `Instances/LTS` cannot import `Examples/`.
- *Parallel trace and collecting paths.* The labeled trace path and
  the unlabeled collecting/fixpoint path are deliberately independent
  structures, because deriving one from the other would require
  assumptions (finite label enumeration, abstract aggregation) that only
  some clients can pay.

# Layered architecture

The repository is a strict, one-directional stack.

: Layer 1 — Semantic core

  `Concretization` (a plain function) and `ConcretizationDomain` (the
  three-field contract). Defines the minimum data required for
  soundness. Contains the generic theorem `gamma_union_subset_sup`.

: Layer 2 — Domain capabilities

  `BottomConcretization`, `PointAbstraction`, `UnaryTransfer`,
  `BinaryTransfer`, `MeetLike`, `FilterOperator`,
  `RelationalBackwardOperator`. Each capability bundles a function with
  its soundness obligation. A domain picks the capabilities it
  genuinely satisfies.

: Layer 3 — Generic soundness and iteration

  Trace lifting (`soundTrace_of_soundStep`), collecting semantics
  (`CollectingStep`, `reachF`, `kleeneNat`, `omegaReachable`), the
  generic fixpoint bridge (`IsPostFixpoint`,
  `sound_iterateNat_from_init_of_isPostFixpoint`,
  `*_subset_of_isPostFixpoint`), and the widening engine
  (`Widen`, `WidenUpperBound`, `WAcc`, `witer`, `pfp`). All
  LTS-agnostic and language-agnostic.

: Layer 4 — CSLib LTS adapters

  `LTSAbstraction` wraps a CSLib `LTS` with a labeled transfer and the
  derived trace-soundness theorem. `LTSCollectingAbstraction` is the
  parallel unlabeled collecting interface bundling a
  `ConcretizationDomain` with `postAny`-soundness. `Analyses/Common.lean`
  provides the readout-based helpers
  (`StepSoundOfRead` / `CollectingSoundOfRead`).

: Layer 5 — IMP adapters and case studies

  `IMPAnalysisDomain`, `transferProgram`, `soundStep_imp`,
  `impAbstraction` (labeled path), plus `transferAnyProgram`,
  `soundAny_imp`, `impCollectingTransfer`, `impReachTransfer`,
  `{kleeneNat,omegaReachableLTS}_subset_of_isPostFixpoint_imp{Sign,Interval,Parity}`
  (collecting path). Showcases: `Showcase`, `LoopShowcase`,
  `WidenShowcase`, `CollectingShowcase`.

# Key interface decisions

: `ConcretizationDomain` replaced a richer `GammaOnlyDomain`

  The earlier design folded join behaviour into the domain structure.
  In practice, join soundness is a theorem from `gamma_monotone` plus
  Mathlib's `SemilatticeSup`. Storing it was duplication.

: Meet is a capability, not a lattice `Inf`

  Some domains have a natural meet that isn't the lattice infimum
  (`intersectParity`); others only need a reductive combinator.
  `MeetLike` captures exactly that.

: Filters and backward operators are capabilities

  A domain can instantiate `ConcretizationDomain` without a branch
  filter; a language whose condition vocabulary never refines an
  abstract value doesn't need to fake one.

: Collecting/fixpoint abstraction is a separate structure

  `LTSAbstraction` takes a labeled transfer; `LTSCollectingAbstraction`
  takes an unlabeled one. Merging them would force extra assumptions
  onto every client.

: `gammaProgram` is program-relative, not a full `ConcretizationDomain`

  IMP's concretization carries an `ActiveIn program` constraint that is
  what makes `soundStep_imp` tractable. That constraint is incompatible
  with `ConcretizationDomain.gamma_top` for arbitrary configurations.
  IMP therefore ships direct specialisations of the framework fixpoint
  theorems (`kleeneNat_subset_of_isPostFixpoint_imp`,
  `omegaReachableLTS_subset_of_isPostFixpoint_imp`) instead of a
  literal `LTSCollectingAbstraction` value.

# Upstream boundary

Realistic CSLib upstream candidates:

- `Concretization`, `ConcretizationDomain`, `gamma_union_subset_sup`;
- the capability layer;
- generic soundness (`Sound`, `SoundStep`, `SoundTrace`,
  `soundTrace_of_soundStep`, `liftTrace`/`liftTracePost`);
- iteration scaffolding (`iterateNat`, `CollectingStep`, `reachF`,
  `kleeneNat`, `omegaReachable_subset_iUnion_kleeneNat`);
- fixpoint/widening layer (`IsPostFixpoint`,
  `*_subset_of_isPostFixpoint`, `Widen`, `WAcc`, `witer`, `pfp`);
- CSLib LTS adapters (`LTSAbstraction`, `LTSCollectingAbstraction`,
  `soundTraceLifted`, `omegaReachableLTS_subset_omegaReachable`,
  `{Step,Collecting}SoundOfRead`).

Pieces that should stay local to this repository:

- IMP syntax, semantics, and `impLTS`;
- `IMPAnalysisDomain` and its per-domain instances;
- `transferProgram` / `transferAnyProgram` and their program-relative
  soundness theorems;
- program-specific showcases and tutorial LTSs.
