import Cslib.Init

import AbsInterpLTS.Domains.Sign
import AbsInterpLTS.Instances.LTS.Analyses.Common

namespace AbsInterpLTS
namespace Instances
namespace LTS
namespace Analyses

open AbsInterpLTS.Framework
open AbsInterpLTS.Domains

universe u v

/-- State concretization for the sign domain via an integer observation function. -/
abbrev SignGamma (State : Type u) := ReadGamma Sign Int State

/-- Lift `gammaSign` to concrete states using a readout `State -> Int`. -/
def gammaSignState
    {State : Type u} :
    SignGamma State :=
  gammaStateOfRead gammaSign

/-- Label-indexed sign transfer family. -/
abbrev SignTransfer (Label : Type v) := Label -> Sign -> Sign

/--
Local one-step sign soundness condition over LTS transitions.

This can be discharged by language-specific transition/transfer lemmas, then
lifted to framework `SoundStep`.
-/
def SignStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : SignTransfer Label) : Prop :=
  StepSoundOfRead gammaSign lts read transfer

/-- Bridge from local sign-transition soundness to framework `SoundStep`. -/
theorem soundStep_postStep_sign_of_stepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : SignTransfer Label)
    (hStep : SignStepSound lts read transfer) :
    SoundStep (postStep lts) (gammaSignState read) transfer := by
  simpa [SignStepSound, gammaSignState] using
    (soundStep_postStep_of_stepSound (gamma := gammaSign) lts read transfer hStep)

/-- Build an LTS abstraction from local sign-step soundness obligations. -/
def signAbstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : SignTransfer Label)
    (hStep : SignStepSound lts read transfer) :
    LTSAbstraction State Label Sign :=
  abstractionOfStepSound (gamma := gammaSign) lts read transfer hStep

end Analyses
end LTS
end Instances
end AbsInterpLTS
