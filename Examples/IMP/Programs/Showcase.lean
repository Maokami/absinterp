import Examples.IMP.Analysis.Sign
import Examples.IMP.Pretty

/-!
Flagship end-to-end IMP case study for the repository.

This file exercises the generic Sign analysis over the canonical labeled IMP
LTS, rather than introducing a separate program-specific toy LTS.

## Axiom note

The `analyzeShowcase_*` theorems use `native_decide` to compute abstract
results along fixed traces. This pulls in `Lean.ofReduceBool` and
`Lean.trustCompiler`. The kernel-only `decide` tactic cannot reduce the
recursive `transferProgramSign` computation within its limits.

The semantic corollaries (`signShowcase_trueTrace_concrete_x0_nonneg`,
`signShowcase_falseTrace_unreachable`) therefore inherit the same
non-standard axioms.

This is acceptable for validation code: the upstream-candidate soundness
path (`soundStep_impSign`, `LTSAbstraction.soundTraceLifted`,
`soundTrace_of_soundStep`) is axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only).
-/

namespace Examples.IMP.Programs

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Instances.LTS
open scoped List

/--
A medium-sized loop-free IMP program written using the example pretty syntax.

It exercises:
- sequencing
- nested conditionals
- abstract expression evaluation
- branch-sensitive Sign refinement on variable tests
-/
def signShowcase : Stmt := [imp|
  x0 := 5 ;;
  if x0 then
    (x1 := x0 + 1 ;;
      if x1 then
        x0 := x1 + x0
      else
        x0 := 0)
  else
    x1 := 0
]

/-- Initial abstract state: start at the program entry with no information. -/
def signShowcaseInit : ConfigSharp Sign :=
  initAt signShowcase topStoreSign

/-- Trace following the reachable outer-then / inner-then path to program exit. -/
def signShowcaseTrueTrace : List StepLabel :=
  [.seqStep .assign, .seqDone, .ifTrue, .seqStep .assign, .seqDone, .ifTrue, .assign]

/-- Prefix reaching the outer true branch after the initial assignment. -/
def signShowcaseOuterTrueTrace : List StepLabel :=
  [.seqStep .assign, .seqDone, .ifTrue]

/-- Prefix reaching the inner true branch just before the final assignment. -/
def signShowcaseInnerTrueTrace : List StepLabel :=
  [.seqStep .assign, .seqDone, .ifTrue, .seqStep .assign, .seqDone, .ifTrue]

/--
Trace selecting the outer false branch after `x0 := 5`.

This trace is semantically impossible from the initial state, and the Sign
analysis detects that by collapsing the branch state to `bot`.
-/
def signShowcaseFalseTrace : List StepLabel :=
  [.seqStep .assign, .seqDone, .ifFalse]

/-- Run the generic IMP Sign analyzer along a fixed trace from the showcase entry state. -/
def analyzeShowcase (labels : List StepLabel) : ConfigSharp Sign :=
  liftTracePostSharp (impSignTransfer signShowcase) labels signShowcaseInit

theorem analyzeShowcase_trueTrace_skip_x0 :
    analyzeShowcase signShowcaseTrueTrace .skip Var.x0 = .nonneg := by
  native_decide

theorem analyzeShowcase_trueTrace_skip_x1 :
    analyzeShowcase signShowcaseTrueTrace .skip Var.x1 = .nonneg := by
  native_decide

theorem analyzeShowcase_outerTrue_x0 :
    analyzeShowcase signShowcaseOuterTrueTrace
      [imp| x1 := x0 + 1 ;; if x1 then x0 := x1 + x0 else x0 := 0] Var.x0 = .pos := by
  native_decide

theorem analyzeShowcase_innerTrue_assign_x0 :
    analyzeShowcase signShowcaseInnerTrueTrace [imp| x0 := x1 + x0] Var.x0 = .pos := by
  native_decide

theorem analyzeShowcase_innerTrue_assign_x1 :
    analyzeShowcase signShowcaseInnerTrueTrace [imp| x0 := x1 + x0] Var.x1 = .pos := by
  native_decide

theorem analyzeShowcase_falseTrace_else_x0 :
    analyzeShowcase signShowcaseFalseTrace [imp| x1 := 0] Var.x0 = .bot := by
  native_decide

/--
Semantic corollary of the computed abstract result:
any concrete execution following the reachable true-trace exits with `x0 >= 0`.
-/
theorem signShowcase_trueTrace_concrete_x0_nonneg
    {σ : Store}
    (hTrace :
      (.skip, σ) ∈
        liftTracePost (postStep impLTS) signShowcaseTrueTrace
          (gammaProgramSign signShowcase signShowcaseInit)) :
    σ Var.x0 = 0 ∨ 0 < σ Var.x0 := by
  have hGamma :
      (.skip, σ) ∈ gammaProgramSign signShowcase (analyzeShowcase signShowcaseTrueTrace) :=
    (impSignAbstraction signShowcase).soundTraceLifted signShowcaseTrueTrace signShowcaseInit hTrace
  rcases (mem_gammaProgramConfigOf_mk).1 hGamma with ⟨_, hStore⟩
  have hx : σ Var.x0 ∈ gammaSign (analyzeShowcase signShowcaseTrueTrace .skip Var.x0) := by
    simpa [analyzeShowcase] using hStore Var.x0
  rw [analyzeShowcase_trueTrace_skip_x0] at hx
  simpa [gammaSign] using hx

/--
Semantic corollary of branch refinement:
the outer false branch is unreachable after the initial `x0 := 5`.
-/
theorem signShowcase_falseTrace_unreachable
    {σ : Store}
    (hTrace :
      ([imp| x1 := 0], σ) ∈
        liftTracePost (postStep impLTS) signShowcaseFalseTrace
          (gammaProgramSign signShowcase signShowcaseInit)) :
    False := by
  have hGamma :
      ([imp| x1 := 0], σ) ∈ gammaProgramSign signShowcase (analyzeShowcase signShowcaseFalseTrace) :=
    (impSignAbstraction signShowcase).soundTraceLifted signShowcaseFalseTrace signShowcaseInit hTrace
  rcases (mem_gammaProgramConfigOf_mk).1 hGamma with ⟨_, hStore⟩
  have hx : σ Var.x0 ∈ gammaSign (analyzeShowcase signShowcaseFalseTrace [imp| x1 := 0] Var.x0) := by
    simpa [analyzeShowcase] using hStore Var.x0
  rw [analyzeShowcase_falseTrace_else_x0] at hx
  simp [gammaSign] at hx

end Examples.IMP.Programs
