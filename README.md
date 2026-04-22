# absinterp

`absinterp` is a Lean 4 repository for reusable abstract interpretation
constructions over CSLib-style LTS semantics.

The project has two linked goals:

1. Build a reusable abstract interpretation framework in Lean 4, centered on
   CSLib's labeled transition system view of semantics.
2. Validate that framework on a small but nontrivial language by implementing
   generic IMP adapters and case studies over the canonical IMP LTS, covering
   both labeled trace soundness and unlabeled collecting/fixpoint reasoning.

The long-term direction is to mature the reusable pieces toward upstream CSLib
contribution, rather than treating this repository as a one-off example dump.

For a layered design overview — goals, design principles, dependency structure,
IMP's role as a validation adapter, and the upstream boundary — see
[`docs/architecture.md`](docs/architecture.md).

A web version of the architecture note, a reading guide, and a
minimal talk deck live in the nested Verso project at [`site/`](site/).
See [`site/README.md`](site/README.md) for local build instructions
and the GitHub Pages publication path. To publish the site, enable
GitHub Pages with **Source = GitHub Actions** in the repository settings.

## What is in place

- A reusable `ConcretizationDomain` kernel plus a capability layer
  (`BottomConcretization`, `MeetLike`, `FilterOperator`,
  `RelationalBackwardOperator`, transfer capabilities).
- A framework layer for concrete/abstract transformers, trace lifting,
  collecting semantics, fixpoint bridges, and widening.
- A CSLib-LTS instantiation layer for both labeled trace abstractions and
  unlabeled collecting abstractions.
- Concrete Sign, Interval, and Parity domains.
- An IMP example suite that exercises both the labeled trace path and the
  collecting/fixpoint path, including a stronger Interval collecting showcase.

## Repository map

- `AbsInterp/Framework`
  Generic reusable core: semantic transformers, soundness, and iteration
  scaffolding.
- `AbsInterp/Instances/LTS`
  CSLib-LTS-specific semantics and the instantiation layer that lifts local
  step soundness to trace soundness.
- `AbsInterp/Domains`
  Concrete abstract domains currently used in the repository.
- `Examples/IMP`
  IMP example suite.
  The main path is:
  `Syntax`/`Semantics`/`LTS`
  -> `Analysis/Generic`
  -> domain wrappers
  -> `Programs/{Showcase,CollectingShowcase}`.
  Tutorial mini-examples live under `Programs/Tutorial`.
- `Tests`
  Smoke tests and theorem-level regression checks across framework, domains,
  LTS instances, and IMP examples.

## Reading order

- Start with `AbsInterp/Framework` if you want the reusable theory.
- Read `AbsInterp/Instances/LTS` next to see how the framework is connected
  to CSLib-style LTS semantics.
- Read `Examples/IMP/Analysis/Generic`, then `Examples/IMP/Analysis/Sign` or
  `Examples/IMP/Analysis/Interval`, and then
  `Examples/IMP/Programs/{Showcase,CollectingShowcase}` for the flagship
  end-to-end case studies.
- Read `Examples/IMP/Programs/Tutorial` only if you want the smaller teaching
  examples first.

## Axiom boundary

The upstream-candidate soundness path (Framework, Instances/LTS, and
the generic IMP analysis) uses only standard axioms (`propext`,
`Quot.sound`, `Classical.choice`). This is enforced at compile time by
`Tests/Axioms.lean`, which uses `#guard_msgs in #print axioms` to pin
the exact axiom set of 13 key declarations.

Some demonstration and test modules
(`Examples/IMP/Programs/Showcase.lean`,
`Examples/IMP/Programs/WidenShowcase.lean`,
`Tests/Examples/IMP/Smoke.lean`,
`Tests/Examples/IMP/ParitySmoke.lean`,
`Tests/Framework/Iteration/Widening.lean`)
intentionally use `native_decide` for computed validation of abstract
analysis output. These modules are clearly marked with axiom-note
documentation and are not part of the upstream-candidate path.

## Build and test

```bash
lake build
lake build Tests
lake test
```

- `lake build` builds the default libraries: `AbsInterp` and `Examples`.
- `lake build Tests` compiles the theorem-style regression suite.
- `lake test` runs the repository test driver, which checks the default
  libraries and the test suite together.

## Development workflow

1. Open a focused issue with Goal, Scope, Deliverables, and Acceptance
   Criteria.
2. Create a branch `issue-<n>-<short-slug>`.
3. Keep changes limited to one coherent work item.
4. Open a PR with a Conventional title and the repository PR template.
5. Validate with `lake build`, `lake build Tests`, and `lake test`.
