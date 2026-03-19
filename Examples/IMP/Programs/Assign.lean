import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS

import Examples.IMP.Syntax
import Examples.IMP.Semantics.Defs

/-!
# Sign Analysis of `x0 := 5`

End-to-end demonstration of the abstract interpretation framework:
1. Define a program-specific LTS encoding `x0 := 5`
2. Connect the Sign domain via `ReadGamma`
3. Prove one-step soundness (`SignStepSound`)
4. Obtain trace soundness automatically (`soundTraceLifted`)
-/

namespace Examples.IMP.Programs

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Instances.LTS
open AbsInterpLTS.Instances.LTS.Analyses

/-! ## Program-specific LTS for `x0 := 5`

State: `(Bool, Int)` — `(before/after, value of x0)`.
A single transition sets x0 to 5.
-/

/-- LTS encoding `x0 := 5`. State = `(pending?, x0 value)`. -/
def assignLTS : Cslib.LTS (Bool × Int) Unit where
  Tr s _ s' := s.1 = true ∧ s'.1 = false ∧ s'.2 = 5

/-- Observe x0 from the state. -/
def readX0Assign : Bool × Int → Int := Prod.snd

/-- Abstract transfer: after `x0 := 5`, the sign is positive. -/
def transferAssign : Unit → Sign → Sign
  | (), _ => .pos

/-! ## Soundness -/

/-- One-step sign soundness for the assignment LTS. -/
theorem stepSoundAssign :
    SignStepSound assignLTS readX0Assign transferAssign := by
  intro _ _ _ s' _ htr
  rcases htr with ⟨_, _, hVal⟩
  simp [gammaStateOfRead, readX0Assign, transferAssign, gammaSign, hVal]

/-- LTS abstraction for `x0 := 5` with the Sign domain. -/
def assignSignAbstraction : LTSAbstraction (Bool × Int) Unit Sign :=
  signAbstractionOfStepSound assignLTS readX0Assign transferAssign stepSoundAssign

/-- Trace soundness obtained for free from one-step soundness. -/
example :
    SoundTrace
      (liftTracePost (postStep assignLTS))
      (gammaSignState readX0Assign)
      (liftTracePostSharp transferAssign) :=
  assignSignAbstraction.soundTraceLifted

end Examples.IMP.Programs
