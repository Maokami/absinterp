# absinterp-lts

`absinterp-lts` is an independent Lean 4 staging repository for reusable abstract interpretation constructions over CSLib semantics.

## Project status

This repository is intentionally in a staged bootstrap phase.

- Repository workflow, CI, and issue tracking are set up first.
- Core modules expose stable interfaces with minimal implementation.
- Detailed formalization is added incrementally through issue-scoped PRs.

## Initial architecture

- `AbsInterpLTS/Core`: semantics-agnostic interfaces (`Post`, soundness shape).
- `AbsInterpLTS/Core/LTS`: direct use of `Cslib.LTS` operators.
- `AbsInterpLTS/Iteration`: iterative approximation scaffolding.
- `AbsInterpLTS/Domains`: sign and interval domain interfaces.
- `AbsInterpLTS/Examples`: placeholders for end-to-end example milestones.

## Build and test

```bash
lake build
lake build Tests
lake test
```

## Development workflow

1. Create an issue.
2. Create a branch `issue-<n>-<short-slug>`.
3. Implement a single staged work item.
4. Open a PR with a Conventional title.
