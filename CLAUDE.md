# CLAUDE.md — absinterp-lts

## Project Overview

`absinterp-lts` is a Lean 4 repository for reusable abstract interpretation
infrastructure over CSLib-style LTS semantics.

The repository is not just collecting toy examples. Its intended shape is:

1. A reusable framework layer that could plausibly inform upstream CSLib work.
2. A CSLib-LTS instantiation layer that turns local step soundness obligations
   into trace soundness results.
3. A concrete end-to-end validation path through loop-free IMP, where a generic
   abstract interpreter is built over the canonical IMP LTS.

The core design choice is **gamma-only** abstraction: no `alpha`, no Galois
connection requirement, soundness first.

## Build & Test

```bash
lake build              # Build default libraries: AbsInterpLTS, Examples
lake build Tests        # Build theorem/regression suite
lake test               # Run the repository test driver
```

All three should pass before opening a PR.

## Repository Architecture

### Reusable core

- `AbsInterpLTS/Framework`
  Generic semantic transformers, trace lifting, soundness interfaces, and
  iteration scaffolding.
- `AbsInterpLTS/Domains`
  Concrete abstract domains used in the repository.

### CSLib-facing layer

- `AbsInterpLTS/Instances/LTS`
  CSLib-LTS semantics, collecting/trace infrastructure, and the abstraction
  interface that packages local step soundness into reusable trace soundness.

### Validation layer

- `Examples/IMP`
  Main case-study tree.
  Recommended reading path:
  `Syntax` -> `Semantics` / `LTS` -> `Abstraction` -> `Analysis/Sign` ->
  `Programs/Showcase`.
- `Examples/IMP/Programs/Tutorial`
  Small teaching examples with program-specific LTSs.
- `Examples/IMP/Programs/Showcase`
  Flagship end-to-end case study over the canonical IMP LTS.

### Tests

- `Tests`
  Smoke/regression files for domains, framework, LTS instances, and IMP.

## File Organization Conventions

- Prefer `Defs.lean`, `Lemmas.lean`, `Soundness.lean`, or similarly focused
  splits once a file stops being easy to scan.
- Use barrel files to expose coherent public entry points for directories.
- Keep tutorial/example code structurally separate from reusable framework code.
- Keep namespaces aligned with conceptual ownership, not just with temporary
  staging convenience.

## Import Discipline

- Framework files must not import from `Instances/`, `Domains/`, or `Examples/`.
- `Instances/LTS` may depend on `Framework`, but not on `Examples/`.
- `Examples/` may depend on framework and instances freely.
- Prefer precise imports when editing focused files; use root barrels when the
  file is intentionally exercising the public surface.

## Proof and Code Style

- Do not change theorem statements or introduce new axioms unless explicitly
  requested.
- Use LSP-first Lean debugging: goals, diagnostics, hover, local search, then
  broader search.
- Separate executable definitions from proof-support lemmas when possible.
- Prefer direct, descriptive theorem names over short local shorthand.
- Keep public docstrings concise and factual.

## Workflow Conventions

- One issue per branch, one branch per PR.
- Branches follow `issue-<n>-<short-slug>`.
- Commits use Conventional format:
  `feat|refactor|fix|test|chore(scope): description`
- PRs should use the repo template and include:
  Summary, Linked issue, Scope, Validation.
- Squash merge is the preferred default.

## Current Quality Bar

- `main` should stay readable as a Lean project, not just as a proof dump.
- The top-level docs should always explain the repo through the CSLib/LTS ->
  generic framework -> IMP case-study story.
- The canonical IMP Sign analysis is the flagship validation path and should
  remain easy to find from the root of the repository.
