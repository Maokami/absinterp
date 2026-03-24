# CLAUDE.md — absinterp-lts

## Project Overview

A reusable abstract interpretation framework built on [cslib](https://github.com/leanprover/cslib) LTS foundations, targeting eventual cslib contribution. Based on the **gamma-only** approach from Xavier Leroy's "Mechanizing Abstract Interpretation" (N40AI, 2024).

**Key design principle**: No `α` (abstraction function). Only `γ` (concretization). Soundness-first, no optimality guarantees required.

## Build & Test

```bash
lake build              # Build default libraries (AbsInterpLTS, Examples)
lake build Examples     # Build example library explicitly
lake build Tests        # Build test suite
lake test               # Run test driver (includes build)
```

All three must pass before any PR. CI runs `lake test` on every push/PR via `.github/workflows/lean_ci.yml`.

## Dependencies

- **mathlib** and **cslib**: pinned at `v4.28.0-rc1` in `lakefile.toml`
- cslib provides `Cslib.LTS`, `LTS.Tr`, `LTS.setImage`, `LTS.MTr`, etc.

## Architecture (3 layers)

```
Framework/              Generic, LTS-agnostic (the reusable core)
  Semantics/            Concrete/Abstract transformers, TraceLift, Collecting
  Soundness/            Sound, SoundStep, SoundTrace + composition/lifting
  Iteration/            iterateNat, kleeneNat (Kleene chain)
  Domains/              GammaOnlyDomain interface

Instances/LTS/          cslib LTS-specific instantiation
  Semantics/            postStep, postTrace, postAny
  Instantiation/        LTSAbstraction structure, trace soundness lifting
  Analyses/             Sign and Interval domain hookups

Domains/                Concrete abstract domains
  Sign.lean             7-point sign lattice
  Interval.lean         bot/range(lo,hi)/top interval domain

Examples/IMP/           Loop-free IMP case study
  Semantics/            Syntax, small-step semantics, and labeled IMP LTS
  Analysis/             Generic Sign analysis over IMP configurations
  Programs/             Small case studies and end-to-end showcase traces
```

**Core theorem chain**: `SoundStep` -> `soundTrace_of_soundStep` -> `SoundTrace`

**User obligation**: prove `SignStepSound` (or similar local 1-step condition) -> get trace soundness for free via `LTSAbstraction.soundTraceLifted`.

## Lean 4 Coding Conventions

### File Organization

- **Defs/Lemmas split**: definitions go in `Foo/Defs.lean`, lemmas/theorems in `Foo/Lemmas.lean`.
- **Barrel imports**: each directory has an aggregator file (e.g., `Semantics.lean` imports all sub-files).
- **One concept per file**: keep files focused. Prefer small files over large monoliths.
- **Namespace matches path**: `AbsInterpLTS.Framework.Soundness.Defs` lives at `Framework/Soundness/Defs.lean`.

### Naming

- **Types/Structures**: `PascalCase` — `Post`, `PostSharp`, `CollectingStep`, `LTSAbstraction`.
- **Definitions/Functions**: `camelCase` — `postStep`, `liftTrace`, `gammaSign`, `composePost`.
- **Theorems/Lemmas**: `camelCase` with descriptive structure:
  - Pattern: `property_subject_condition` — e.g., `postStep_monotone`, `joinSign_sound`.
  - Lifting theorems: `resultProperty_of_assumption` — e.g., `soundTrace_of_soundStep`, `sound_iterateNat_of_sound`.
  - Simp lemmas: `subject_pattern` — e.g., `liftTracePost_nil`, `liftTracePost_cons`, `kleeneNat_succ`.
  - Membership: `mem_subject_condition` — e.g., `mem_postAny`, `mem_postAny_singleton_iff`.
- **Concrete vs Abstract**: concrete uses plain names (`Post`, `composePost`), abstract appends `Sharp` (`PostSharp`, `composePostSharp`).
- **Private helpers**: mark with `private` for file-internal lemmas (e.g., `private theorem composePost_assoc`).

### Type Aliases and Abbreviations

- Use `abbrev` for transparent type aliases that should unfold: `abbrev Post (State) := Set State -> Set State`.
- Use `def` for opaque definitions that should not auto-unfold.
- Universe polymorphism: use explicit `universe u v w` declarations.

### Proof Style

- **Tactic mode preferred** for non-trivial proofs.
- **Term mode** acceptable for short proofs (1-2 lines) or direct applications.
- **`calc` blocks** for chain reasoning (see `sound_iterateNat_of_sound`).
- **Structure proofs by cases**: use `cases ... with` or `rcases` for inductive types.
- **Induction**: prefer `induction ... with` syntax with named cases (`| nil =>`, `| cons label labels ih =>`).
- **Avoid `sorry`**: all theorems must be fully proved. Use `sorry` only during development, never in committed code.
- **`simp` discipline**:
  - Mark definitional unfolding lemmas with `@[simp]` (e.g., `reachF_apply`, `kleeneNat_succ`).
  - Use `simp [specific_lemmas]` rather than bare `simp` when possible.
  - Use `simpa` for simplification + exact matching.
- **`omega`** for integer/natural number arithmetic goals.
- **Monotonicity arguments**: the pattern `hMono (h_subset)` to transport subset through monotone functions is common throughout.
- **`change` tactic**: use to rewrite goal/hypothesis to a definitionally equal but more readable form (see `Sign.lean` proofs).
- **Proof decomposition**: factor auxiliary steps into `have` bindings for readability.
- **`exact`/`apply`** over `assumption`: be explicit about which lemma closes the goal.

### Definitions and Structures

- **Structure fields**: use descriptive names matching framework vocabulary (`lts`, `gamma`, `transfer`, `soundStep`).
- **Constructors**: provide convenience constructors when the structure has many fields (e.g., `LTSAbstraction.ofExplicit`).
- **Section/variable**: use `section`/`variable` to factor common parameters in related definitions.
- **Docstrings**: use `/-- ... -/` for all public definitions and theorems. Keep them concise (1-2 sentences). Use `/-! ... -/` for module-level documentation.

### Import Discipline

- Import `Cslib.Init` as baseline for cslib interop.
- Import specific Mathlib modules (e.g., `Mathlib.Data.Set.Lattice`, `Mathlib.Order.Monotone.Defs`) rather than bulk imports.
- Framework files must NOT import from `Instances/` or `Domains/` (layering invariant).

## Workflow Conventions

### Branching

- Branch name: `issue-<n>-<short-slug>` (e.g., `issue-29-gamma-only-core-split`).
- One issue per branch, one branch per PR.

### Commits

- Conventional commits: `feat|refactor|fix|test|chore(scope): description`
- Examples from history:
  - `feat(interval): prove meetInterval soundness`
  - `refactor(framework): extract gamma-only domain contract and wire Sign/Interval`
  - `test(lts): add postTrace bridge smoke checks`

### Pull Requests

- Title: Conventional format, under 70 characters.
- Use the PR template (Summary, Linked issue, Scope, Validation checklist).
- Always link to the issue with `Closes #N`.
- **Squash merge** preferred: merge via `gh pr merge --squash` so each PR becomes a single atomic commit on `main`.

### Issues

- Use the staged work item template.
- Must include: Goal, Scope, Out of Scope, Deliverables, Acceptance Criteria.
- All acceptance criteria include `lake build`, `lake build Tests`, `lake test` passing.

## Active Milestones

- **M4**: Semantics Extensions (weak/tau, omega) — see #16
- **M5**: N40AI Gamma-Only Core Alignment — see #33

## Lean LSP MCP Tools

When writing or debugging proofs, use MCP tools:

- `lean_goal`: check proof state at a position (most frequently used)
- `lean_diagnostic_messages`: check for compiler errors
- `lean_hover_info`: inspect type signatures
- `lean_multi_attempt`: test multiple tactics without editing (`["simp", "omega", "tauto"]`)
- `lean_local_search`: find local declarations by name
- `lean_leansearch` / `lean_loogle`: search mathlib for lemmas
- `lean_state_search`: find lemmas that close a goal
- `lean_build`: rebuild after adding new imports (slow, use sparingly)
