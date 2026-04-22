import VersoManual

open Verso.Genre Manual

#doc (Manual) "Reading Guide" =>
%%%
tag := "reading-guide"
%%%

A compact reader path through the repository.

# If you want the reusable theory

Start at the semantic kernel and walk outward.

- `AbsInterp/Framework/Concretization.lean`
- `AbsInterp/Framework/Domains/Concretization.lean`
  — the `ConcretizationDomain` contract and `gamma_union_subset_sup`.
- `AbsInterp/Framework/Domains/Capabilities.lean` and siblings
  (`BottomConcretization`, `PointAbstraction`, `FilterOperator`,
  `RelationalBackwardOperator`, `MeetLike`, transfer capabilities).
- `AbsInterp/Framework/Soundness/` — one-step, step, and trace soundness
  predicates plus trace lifting.
- `AbsInterp/Framework/Iteration/` — `iterateNat`, `Collecting`,
  `Fixpoint/`, `Widening/`.

# If you want the CSLib integration

- `AbsInterp/Instances/LTS/Semantics/` — `Concrete`, `Collecting`,
  `Omega`, `Weak`.
- `AbsInterp/Instances/LTS/Instantiation/Interface.lean` —
  `LTSAbstraction` for the labeled trace path.
- `AbsInterp/Instances/LTS/Instantiation/CollectingInterface.lean` —
  `LTSCollectingAbstraction` for the unlabeled collecting path.
- `AbsInterp/Instances/LTS/Instantiation/{Soundness,CollectingSoundness}.lean`
  — the derived soundness theorems.
- `AbsInterp/Instances/LTS/Analyses/Common.lean` — readout helpers
  (`StepSoundOfRead`, `CollectingSoundOfRead`).

# If you want the IMP case study

- `Examples/IMP/Syntax.lean`, `Semantics/`, `LTS.lean` — the concrete
  language.
- `Examples/IMP/Abstraction/` — `ConfigSharp`, `StoreSharp`,
  `gammaConfigOf`, `gammaProgramConfigOf`.
- `Examples/IMP/Analysis/Generic/Domain.lean` — `IMPAnalysisDomain`.
- `Examples/IMP/Analysis/Generic/{Defs,Lemmas,Soundness}.lean` — the
  labeled transfer + `soundStep_imp` + `impAbstraction`.
- `Examples/IMP/Analysis/Generic/Collecting.lean` — the unlabeled
  `transferAnyProgram`, `soundAny_imp`, and the IMP bridge theorems.
- `Examples/IMP/Analysis/{Sign,Interval,Parity}/Defs.lean` — thin
  per-domain wrappers.
- `Examples/IMP/Programs/Showcase.lean` — labeled Sign showcase.
- `Examples/IMP/Programs/CollectingShowcase.lean` — Interval value
  invariant `x0 = 5` via the collecting bridge.
- `Examples/IMP/Programs/WidenShowcase.lean` — widening demo.

# Session-by-session evolution

The repository's current shape is the result of several focused sessions.
The following list orients a new reader to what each session contributed.

- *Session 1* — canonicalised the γ-only domain contract
  (`GammaOnlyDomain` → `ConcretizationDomain`); join soundness became
  a generic theorem.
- *Session 2* — soundness transport: one-step → trace lifting,
  packaged as `LTSAbstraction.soundTraceLifted`.
- *Session 3* — scalar domain cleanup: stale `Max` / `join_sound` API
  removed; interval widening moved into a dedicated module.
- *Session 4* — the generic fixpoint bridge: `IsPostFixpoint` and
  `sound_of_isPostFixpoint` moved out of the widening module; new
  `sound_iterateNat_from_init_of_isPostFixpoint`,
  `kleeneNat_subset_of_isPostFixpoint`,
  `omegaReachable_subset_of_isPostFixpoint`.
- *Session 5* — CSLib LTS collecting adapter:
  `LTSCollectingAbstraction`, `sound_reachTransfer`,
  `omegaReachableLTS_subset_of_isPostFixpoint`, the readout helper
  `CollectingSoundOfRead`.
- *Session 6* — IMP collecting adapter: `transferAnyProgram`,
  `soundAny_imp`, `impCollectingTransfer`, the thin Sign/Interval/Parity
  wrappers, and the first `CollectingShowcase` smoke test.
- *Issue #113* — strengthened IMP collecting showcase:
  `CollectingShowcase` now proves `x0 = 5` at the while head of the
  flagship program via a hand-written Interval post-fixpoint,
  axiom-clean (no `native_decide`).

# Strongest showcase artifacts

- *Labeled trace path:* `Examples/IMP/Programs/Showcase.lean`.
- *Unlabeled collecting/fixpoint path:*
  `Examples/IMP/Programs/CollectingShowcase.lean` — the current flagship,
  proving a concrete value invariant.
- *Widening:* `Examples/IMP/Programs/WidenShowcase.lean`.
- *Axiom hygiene check:* `Tests/Axioms.lean`.
