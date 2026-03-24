# absinterp-lts

`absinterp-lts` is an independent Lean 4 repository for reusable abstract interpretation constructions over CSLib semantics.

## Project status

The project now has a usable core:

- a reusable `gamma`-only abstract interpretation framework over LTS-style semantics
- a CSLib-LTS instantiation with soundness lifting from one-step to traces
- collecting-semantics infrastructure and a collecting/trace bridge
- concrete Sign and Interval domains
- a loop-free IMP case study showing how to build a generic abstract interpreter on top of the framework

The remaining staged work is mostly about broadening coverage: more domains,
more iteration/fixpoint case studies, and richer language examples.

## Initial architecture

- `AbsInterpLTS/Framework`: language-agnostic abstract interpretation framework.
  - `Semantics`: concrete/abstract transformer interfaces and trace lifting.
  - `Soundness`: one-step/trace soundness predicates and lifting obligations.
  - `Iteration`: iterative approximation scaffolding.
- `AbsInterpLTS/Instances/LTS`: CSLib-LTS instance of the framework.
  - `Semantics`: LTS concrete semantics and LTS-specific properties.
  - `Instantiation`: framework-to-LTS abstraction/soundness instantiation layer.
  - `Analyses`: domain-specific analysis instances over LTS (staged).
- `AbsInterpLTS/Domains`: sign and interval domain interfaces.
- `Examples/IMP`: a loop-free IMP case study with a generic Sign analysis over
  the canonical IMP LTS.

## Build and test

```bash
lake build
lake build Examples
lake build Tests
lake test
```

`lake build` builds the main library and the example library. `lake test`
checks that the default libraries and the test suite both compile.

## Development workflow

1. Create an issue from the staged work-item template.
2. Create a branch `issue-<n>-<short-slug>`.
3. Implement a single staged work item.
4. Open a PR with a Conventional title.
