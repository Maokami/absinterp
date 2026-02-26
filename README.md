# absinterp-lts

`absinterp-lts` is an independent Lean 4 staging repository for reusable abstract interpretation constructions over CSLib semantics.

## Project status

This repository is intentionally in a staged bootstrap phase.

- Repository workflow, CI, and issue tracking are set up first.
- Framework modules expose stable interfaces with minimal implementation.
- Detailed formalization is added incrementally through issue-scoped PRs.

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

## Build and test

```bash
lake build
lake build Tests
lake test
```

## Development workflow

1. Create an issue from the staged work-item template.
2. Create a branch `issue-<n>-<short-slug>`.
3. Implement a single staged work item.
4. Open a PR with a Conventional title.
