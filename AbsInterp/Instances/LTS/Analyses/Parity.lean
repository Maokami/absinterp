import Cslib.Init

import AbsInterp.Domains.Parity
import AbsInterp.Instances.LTS.Analyses.Common

namespace AbsInterp
namespace Instances
namespace LTS
namespace Analyses

open AbsInterp.Framework
open AbsInterp.Domains

universe u v

/-- State concretization for the parity domain via an integer observation function. -/
abbrev ParityGamma (State : Type u) := ReadGamma Parity Int State

/-- Lift `gammaParity` to concrete states using a readout `State -> Int`. -/
def gammaParityState
    {State : Type u} :
    ParityGamma State :=
  gammaStateOfRead gammaParity

/-- Label-indexed parity transfer family. -/
abbrev ParityTransfer (Label : Type v) := Label -> Parity -> Parity

/--
Local one-step parity soundness condition over LTS transitions.

This can be discharged by language-specific transition/transfer lemmas, then
lifted to framework `SoundStep`.
-/
def ParityStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : ParityTransfer Label) : Prop :=
  StepSoundOfRead gammaParity lts read transfer

/-- Bridge from local parity-transition soundness to framework `SoundStep`. -/
theorem soundStep_postStep_parity_of_stepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : ParityTransfer Label)
    (hStep : ParityStepSound lts read transfer) :
    SoundStep (postStep lts) (gammaParityState read) transfer := by
  simpa [ParityStepSound, gammaParityState] using
    (soundStep_postStep_of_stepSound (gamma := gammaParity) lts read transfer hStep)

/-- Build an LTS abstraction from local parity-step soundness obligations. -/
def parityAbstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : ParityTransfer Label)
    (hStep : ParityStepSound lts read transfer) :
    LTSAbstraction State Label Parity :=
  abstractionOfStepSound (gamma := gammaParity) lts read transfer hStep

end Analyses
end LTS
end Instances
end AbsInterp
