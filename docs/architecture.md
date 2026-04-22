# Architecture Note: Layered Abstract Interpretation over CSLib-style LTS

`absinterp` is a Lean 4 repository for reusable abstract-interpretation
infrastructure organized as a small stack of layers over CSLib-style labeled
transition systems. IMP serves as the main validation case study, not as the
primary artifact. The long-term direction is to mature the lower layers into
contributions to `leanprover/cslib`.

## 1. Goals

Two linked goals drive the project.

**Build a reusable AI framework in Lean 4.** The target is reusable theory and
infrastructure — semantic transformers, soundness interfaces, iteration
scaffolding, and LTS-facing adapters — that another language or another abstract
domain can plug into without re-proving boilerplate. The design is
soundness-first: every abstract operation comes with a concretization-level
soundness obligation, and trace/collecting/omega soundness is derived from
one-step obligations via generic theorems.

**Validate that framework on a non-trivial but manageable language.** IMP plays
that role. The IMP case study exercises the labeled trace path
(`soundStep → soundTrace`), the unlabeled collecting/fixpoint path
(`postAny → reachF → kleeneNat → omegaReachable`), and the widening iteration
interface. If the framework breaks or is awkward, the IMP path is where the
friction surfaces first.

Two explicit non-goals: no Galois connection is required (the project stays
γ-only), and no ambition to ship an industrial IMP analyzer. The value lives in
the reusable layers below `Examples/IMP`.

## 2. Design principles

**Soundness first.** Every abstract operation is accompanied by a
concretization-level soundness statement. `Tests/Axioms.lean` pins the axiom
footprint of thirteen upstream-candidate declarations to `propext`, `Quot.sound`,
`Classical.choice` via `#guard_msgs`, and the build enforces this. Computation-
heavy showcases that use `native_decide` are explicitly quarantined outside
that path.

**Keep the semantic kernel small.** The core interface, `ConcretizationDomain`,
carries only `gamma`, `gamma_monotone`, and `gamma_top`. Anything else is
either derived from these (join soundness) or packaged as an opt-in capability.
A minimal kernel is what lets the same framework host simple domains like
`Sign`, lattice-structured domains like `Interval`, and potential relational
domains in the future without forcing structure none of them naturally carry.

**Separate domain meaning from analysis operations.** `ConcretizationDomain`
says *what the abstract values mean*. Filters, backward operators, and binary
transfers live above that, as explicit capabilities. The benefit is
composability: a language adapter picks exactly the capabilities it needs, and
every capability carries its own soundness law. A two-domain analysis, or a
relational analysis that doesn't want `filterNonzero`, doesn't have to fake one.

**Keep framework core and language adapters structurally separate.**
`AbsInterp/Framework` cannot import from `Instances/` or `Examples/`.
`Instances/LTS` cannot import `Examples/`. IMP-specific arithmetic —
`IMPAnalysisDomain`, `transferProgram`, `gammaProgram` — lives entirely in the
`Examples/IMP` adapter and cannot leak upward.

**Do not force more algebraic structure than necessary in the core.**
Deliberate examples: join soundness is a generic theorem from `SemilatticeSup`
plus `gamma_monotone`, not a structure field. Meet is expressed as `MeetLike`
(binary soundness + reductiveness) instead of a full lattice `Inf`. This keeps
domains with asymmetric join/meet — or domains that only need a single
combinator — admissible as first-class citizens.

**Keep collecting/fixpoint reasoning parallel to the labeled trace path.** The
labeled path (`LTSAbstraction`, `soundTraceLifted`) and the unlabeled
collecting/fixpoint path (`LTSCollectingAbstraction`,
`omegaReachableLTS_subset_of_isPostFixpoint`) are deliberately independent
structures. A labeled transfer (`Label → Abstract → Abstract`) has more
information than an unlabeled collecting transfer (`Abstract → Abstract`), and
deriving one from the other requires assumptions (finite label enumeration,
abstract aggregation) that only some clients can pay. Splitting the interfaces
reflects that.

## 3. Layered architecture

The repository is organized as a strict, one-directional stack. Every layer
depends only on layers below it.

**Layer 1 — Semantic core.** `AbsInterp/Framework/Concretization.lean` and
`AbsInterp/Framework/Domains/Concretization.lean`. Defines `Concretization` (a
plain function type) and `ConcretizationDomain` (the three-field contract). The
generic theorem `gamma_union_subset_sup` lives here: join soundness follows
from `gamma_monotone` and `SemilatticeSup`. This is the only layer all other
layers depend on.

**Layer 2 — Domain capabilities.** `AbsInterp/Framework/Domains/Capabilities.lean`
and siblings. `BottomConcretization`, `PointAbstraction`, `UnaryTransfer`,
`BinaryTransfer`, `MeetLike`, `FilterOperator`, `RelationalBackwardOperator`.
Each capability bundles a function with its soundness obligation (and
reductiveness where applicable). A domain picks the capabilities it actually
satisfies; it does not have to commit to all of them. The `AbsInterp/Domains`
instances (`Sign`, `Parity`, `Interval`) show the intended shape.

**Layer 3 — Generic soundness and iteration.**
`AbsInterp/Framework/Soundness/`, `AbsInterp/Framework/Iteration/NatIter.lean`,
`Iteration/Collecting.lean`, `Iteration/Fixpoint/`, `Iteration/Widening/`.
Contains:

- trace lifting (`soundTrace_of_soundStep`, `liftTracePost`/`liftTracePostSharp`);
- collecting semantics (`CollectingStep`, `reachF`, `kleeneNat`) and
  `omegaReachable`;
- the generic fixpoint bridge (`IsPostFixpoint`,
  `sound_iterateNat_from_init_of_isPostFixpoint`, the
  `*_subset_of_isPostFixpoint` specialisations to `kleeneNat` and
  `omegaReachable`);
- the widening engine (`Widen`, `WidenUpperBound`, `WAcc`, `witer`, `pfp`,
  `isPostFixpoint_pfp`).

Everything in Layer 3 is LTS-agnostic and language-agnostic. The split of
`IsPostFixpoint` out of `Widening/` was deliberate: post-fixpoint soundness is
not a widening concept, and the collecting/omega corollaries reuse it without
pulling in `WAcc`.

**Layer 4 — CSLib LTS adapters.** `AbsInterp/Instances/LTS`. Wraps CSLib's
`LTS`/`MTr`/`ωTr`/`HasTau` into the framework's vocabulary.

- `LTSAbstraction` packages a CSLib LTS with a labeled `transfer : Label →
  Abstract → Abstract`, a step-soundness proof, and the derived
  `soundTraceLifted` theorem.
- `LTSCollectingAbstraction` is the *parallel* collecting interface: it carries
  an unlabeled `transferAny`, a `ConcretizationDomain`, and a soundness proof
  for `postAny`. It provides the reach-transfer and the headline
  `omegaReachableLTS_subset_of_isPostFixpoint` bridge.
- `Analyses/Common.lean` hosts the readout-based helpers
  (`StepSoundOfRead`/`CollectingSoundOfRead`) so domain-specific hooks can
  build either abstraction from a state-observation function.

**Layer 5 — IMP adapters and case studies.** `Examples/IMP`.

- `IMPAnalysisDomain` is the IMP-specific capability bundle (arithmetic
  transfers, branch filters, backward operators).
- The labeled path: `transferProgram`, `soundStep_imp`, `impAbstraction`, with
  thin wrappers in `Analysis/{Sign,Interval,Parity}/Defs.lean`.
- The collecting path: `transferAnyProgram`, `soundAny_imp`,
  `impCollectingTransfer`, `impReachTransfer`, and the
  `{kleeneNat,omegaReachableLTS}_subset_of_isPostFixpoint_imp{Sign,Interval,Parity}`
  corollaries.
- Programs: `Showcase` (labeled Sign trace analysis), `LoopShowcase`,
  `WidenShowcase`, and `CollectingShowcase` (the Interval `x0 = 5` value
  invariant consumer of the Session 4/5 bridge).

The dependency direction is strict. Layer 5 sits above Layer 4, which sits
above Layer 3, and so on. Nothing in Layer 4 or below mentions IMP.

## 4. Why the current interfaces look the way they do

**`ConcretizationDomain` replaced an earlier `GammaOnlyDomain`.** The old
interface tried to fold join behaviour into the domain structure. In practice,
join soundness is a theorem from `gamma_monotone` plus an existing `Sup`
instance, so stored fields just duplicated Mathlib's lattice hierarchy.
`ConcretizationDomain` is now the narrowest thing that *must* be true, and
`SemilatticeSup`/`OrderTop` come from Mathlib instances on each concrete
domain. Join soundness is derived, not stored.

**`MeetLike` is a capability, not a fully-fledged lattice `Inf`.** Some domains
have a natural meet that isn't the lattice infimum (`intersectParity`);
others may want a combinator that is reductive but not idempotent. Treating
meet as a capability captures exactly the property the IMP transfer actually
needs (`refineAddStore` for `x = x` case) without imposing a lattice
obligation the domain might not carry cleanly.

**Filter and backward operators are capabilities, not core fields.** A
domain can instantiate `ConcretizationDomain` without a branch filter; a
language whose condition language never refines an abstract value doesn't need
to fake one. By contrast, the labeled `transferProgram` recursion *does* need a
filter for `.ite` and `.while`, so it demands `FilterOperator` at the
adapter level, not at the core.

**Collecting/fixpoint abstraction is a separate structure from
`LTSAbstraction`.** `LTSAbstraction` takes a labeled transfer and targets
trace soundness. `LTSCollectingAbstraction` takes an unlabeled transfer and
targets reachability/fixpoints. Overloading would have required injecting
either finite-label enumeration or abstract aggregation into the core; both
assumptions are real costs that not every language can pay.

**`gammaProgram` is deliberately *not* a `ConcretizationDomain`.** The IMP
concretization is program-relative: it carries an `ActiveIn program`
constraint on the control location. That constraint is what lets
`soundStep_imp` avoid having to handle arbitrary non-active control states.
But `ConcretizationDomain.gamma_top` requires `∀ c, c ∈ gamma ⊤`, which would
force program-irrelevant configurations back into scope. Instead, IMP provides
its bridge theorems (`kleeneNat_subset_of_isPostFixpoint_imp`,
`omegaReachableLTS_subset_of_isPostFixpoint_imp`) as direct specialisations of
the framework-level fixpoint theorems that accept a plain `Concretization` plus
`gamma_monotone`. The spec's preferred "literal `LTSCollectingAbstraction`
value for IMP" is not realisable without either subtyping `Config` to active
configurations or weakening the framework interface; neither is worth it for
the benefit.

**Axiom-cleanliness is a first-class constraint.** The upstream-candidate path
stays on `propext`, `Quot.sound`, `Classical.choice`. `native_decide` (which
introduces `Lean.ofReduceBool` and `Lean.trustCompiler`) is confined to
validation computations in showcases and tests. The newest IMP
`CollectingShowcase` proves `x0 = 5` at the loop head via a hand-written
post-fixpoint precisely so the flagship collecting invariant stays in the
axiom-clean region.

## 5. Case-study role of IMP

IMP is a validation adapter, not the product. Its job is to exercise every
reusable layer end-to-end and to be specific enough that the framework's
genericity can be measured.

- **Labeled trace path.** `soundStep_impSign` combines with
  `LTSAbstraction.soundTraceLifted` to yield `SoundTrace` for the Sign
  analysis, consumed in `Programs/Showcase.lean`.
- **Unlabeled collecting/fixpoint path.** `soundAny_imp` plus the generic
  fixpoint bridge gives `omegaReachableLTS_subset_of_isPostFixpoint_imp`.
  `Programs/CollectingShowcase.lean` proves a genuine value invariant
  (`x0 = 5` at the while head of `x0 := 5;; while x0 do x0 := x0 + 0`) through
  this path.
- **Widening path.** `Programs/WidenShowcase.lean` exercises the widening
  interface (`WidenUpperBound`, `WAcc`, `pfp`, `isPostFixpoint_pfp`) on an
  Interval analysis.
- **Tutorial examples.** `Programs/Tutorial/` contains small standalone LTSs
  for readers who want to understand the interfaces without the full IMP LTS.

IMP's arithmetic specificity is tolerated because it lives strictly above the
reusable layers. No IMP identifier appears in `AbsInterp/Framework` or
`AbsInterp/Instances/LTS`.

## 6. Upstream boundary

These pieces are realistic CSLib upstream candidates once packaged:

- `Concretization`, `ConcretizationDomain`, `gamma_union_subset_sup`;
- the capability layer (`BottomConcretization`, `MeetLike`, `PointAbstraction`,
  `FilterOperator`, `RelationalBackwardOperator`, `UnaryTransfer`,
  `BinaryTransfer`);
- generic soundness infrastructure (`Sound`, `SoundStep`, `SoundTrace`,
  `soundTrace_of_soundStep`, `liftTrace`/`liftTracePost`);
- iteration scaffolding (`iterateNat`, `CollectingStep`, `reachF`, `kleeneNat`,
  `omegaReachable_subset_iUnion_kleeneNat`);
- the fixpoint/widening layer (`IsPostFixpoint`,
  `sound_iterateNat_from_init_of_isPostFixpoint`,
  `*_subset_of_isPostFixpoint`, `Widen`, `WidenUpperBound`, `WAcc`, `witer`,
  `pfp`, `isPostFixpoint_pfp`);
- the CSLib LTS adapter layer (`LTSAbstraction`, `LTSCollectingAbstraction`,
  `soundTraceLifted`, `omegaReachableLTS_subset_omegaReachable`,
  `CollectingSoundOfRead` / `StepSoundOfRead`).

These pieces should stay local to this repository:

- the IMP syntax, semantics, and `impLTS`;
- `IMPAnalysisDomain` and its per-domain instances;
- `transferProgram`/`transferAnyProgram` and their program-relative soundness
  theorems;
- program-specific showcases (`Showcase`, `LoopShowcase`, `WidenShowcase`,
  `CollectingShowcase`);
- tutorial LTSs.

The split is principled: anything that mentions IMP, IMP arithmetic, or a
specific program belongs above the framework boundary.

## 7. Current limitations and future work

- **Proof robustness.** Some collecting showcase proofs rely on structural
  unfolding of `transferAnyProgram`; if it migrates to well-founded recursion,
  those `rfl` finishers need explicit equation rewrites.
- **Domain coverage.** Only Sign, Parity, and Interval are packaged. Relational
  domains (congruences, pairwise difference) are natural next targets and
  would stress the kernel's minimality.
- **Widening and solver stories.** Widening is wired on simple finite flat
  lattices; realistic config-level widening (`IntervalConfigSharp`) and
  narrowing are not yet packaged as reusable solver combinators.
- **Weak/τ path.** `Weak`/`HasTau` support exists but has not been exercised in
  an end-to-end case study at the collecting/omega layer.
- **Upstream packaging.** Namespaces, docstrings, and Mathlib-style linting
  still need a sweep before a serious first CSLib PR.

## 8. Repository map

- `AbsInterp/Framework` — Layers 1–3 (semantic kernel, capabilities, generic
  soundness, iteration, fixpoint, widening).
- `AbsInterp/Instances/LTS` — Layer 4 (CSLib LTS adapters, including both
  labeled trace and unlabeled collecting interfaces).
- `AbsInterp/Domains` — concrete scalar domains (`Sign`, `Parity`, `Interval`)
  with their capability instances.
- `Examples/IMP` — Layer 5 (IMP adapter, per-domain instances, programs).
- `Tests` — regression tests, axiom guards, and framework-level smoke tests.

Start from `AbsInterp/Framework/Domains/Concretization.lean` if you want the
semantic kernel; from `AbsInterp/Instances/LTS/Instantiation/CollectingInterface.lean`
if you want the CSLib integration; from
`Examples/IMP/Programs/CollectingShowcase.lean` if you want to see the full
pipeline land on a concrete value invariant.
