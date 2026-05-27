import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterp.Domains
import AbsInterp.Framework
import AbsInterp.Instances.LTS
import AbsInterp.Instances.LTS.Analyses.Sign

import Examples.IMP.Semantics

/-!
# Sign Analysis of `x0 := 5; if x0 then x0 := x0 + 1 else x0 := 0`

Demonstrates multi-label Sign analysis on a branching IMP program.
The transfer function exploits branch conditions for precision:
- `takeThen` guard (`x0 ≠ 0`) eliminates `zero` from the abstract state
- `takeElse` guard (`x0 = 0`) pins the result to `.zero`
-/

namespace Examples.IMP.Programs.Tutorial

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Instances.LTS
open AbsInterp.Instances.LTS.Analyses

/-! ## Program-specific LTS

```
init -[assignFive]-> test -[takeThen]-> doneTrue
                          -[takeElse]-> doneFalse
```
-/

/-- Program counter for the branch program. -/
inductive BranchPC where
  | init
  | test
  | doneTrue
  | doneFalse
  deriving DecidableEq, Repr

/-- Transition labels for the branch program. -/
inductive BranchLabel where
  | assignFive
  | takeThen
  | takeElse
  deriving DecidableEq, Repr

/-- LTS for `x0 := 5; if x0 then x0 := x0 + 1 else x0 := 0`.
    State = `(PC, x0 value)`. -/
def branchLTS : Cslib.LTS (BranchPC × Int) BranchLabel where
  Tr s label s' := match label with
    | .assignFive => s.1 = .init ∧ s'.1 = .test ∧ s'.2 = 5
    | .takeThen   => s.1 = .test ∧ s.2 ≠ 0 ∧ s'.1 = .doneTrue ∧ s'.2 = s.2 + 1
    | .takeElse   => s.1 = .test ∧ s.2 = 0 ∧ s'.1 = .doneFalse ∧ s'.2 = 0

/-- Observe x0 from the state. -/
def readX0Branch : BranchPC × Int → Int := Prod.snd

/--
Abstract transfer for the branch program.

Key precision gains from branch conditions:
- `.takeThen, .zero => .bot`: x0 = 0 cannot take the true branch (vacuously sound)
- `.takeThen, .pos => .pos`: positive + 1 is positive
- `.takeThen, .nonneg => .pos`: nonneg ∧ ≠ 0 means positive, +1 stays positive
-/
def transferBranch : BranchLabel → Sign → Sign
  | .assignFive, _ => .pos
  | .takeThen, .bot => .bot
  | .takeThen, .neg => .nonpos
  | .takeThen, .zero => .bot
  | .takeThen, .pos => .pos
  | .takeThen, .nonpos => .nonpos
  | .takeThen, .nonneg => .pos
  | .takeThen, .top => .top
  | .takeElse, _ => .zero

/-! ## Soundness -/

/-- One-step sign soundness for the branch LTS. -/
theorem stepSoundBranch :
    SignStepSound branchLTS readX0Branch transferBranch := by
  intro label a s s' hs htr
  cases label with
  | assignFive =>
    rcases htr with ⟨_, _, hVal⟩
    simp [gammaStateOfRead, readX0Branch, transferBranch, gammaSign, hVal]
  | takeThen =>
    rcases htr with ⟨_, hNe, _, hVal⟩
    simp [gammaStateOfRead, readX0Branch, transferBranch, hVal] at hs ⊢
    cases a with
    | bot => exact absurd hs (by simp [gammaSign])
    | neg => simp [gammaSign] at hs ⊢; omega
    | zero => simp [gammaSign] at hs; omega
    | pos => simp [gammaSign] at hs ⊢; omega
    | nonpos => simp [gammaSign] at hs ⊢; omega
    | nonneg => simp [gammaSign] at hs ⊢; omega
    | top => simp [gammaSign]
  | takeElse =>
    rcases htr with ⟨_, _, _, hVal⟩
    simp [gammaStateOfRead, readX0Branch, transferBranch, gammaSign, hVal]

/-- LTS abstraction for the branch program with the Sign domain. -/
def branchSignAbstraction : LTSAbstraction (BranchPC × Int) BranchLabel Sign :=
  signAbstractionOfStepSound branchLTS readX0Branch transferBranch stepSoundBranch

/-- Trace soundness obtained for free from one-step soundness. -/
example :
    SoundTrace
      (liftTracePost (postStep branchLTS))
      (gammaSignState readX0Branch)
      (liftTracePostSharp transferBranch) :=
  branchSignAbstraction.soundTraceLifted

end Examples.IMP.Programs.Tutorial
