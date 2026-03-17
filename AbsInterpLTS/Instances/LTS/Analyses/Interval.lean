import Cslib.Init

import AbsInterpLTS.Domains.Interval
import AbsInterpLTS.Instances.LTS.Analyses.Common

namespace AbsInterpLTS
namespace Instances
namespace LTS
namespace Analyses

open AbsInterpLTS.Framework
open AbsInterpLTS.Domains

universe u v

/-- State concretization for the interval domain via an integer observation function. -/
abbrev IntervalGamma (State : Type u) := ReadGamma Interval Int State

/-- Lift `gammaInterval` to concrete states using a readout `State -> Int`. -/
def gammaIntervalState
    {State : Type u} :
    IntervalGamma State :=
  gammaStateOfRead gammaInterval

/-- Label-indexed interval transfer family. -/
abbrev IntervalTransfer (Label : Type v) := Label -> Interval -> Interval

/--
Local one-step interval soundness condition over LTS transitions.

This can be discharged by language-specific transition/transfer lemmas, then
lifted to framework `SoundStep`.
-/
def IntervalStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : IntervalTransfer Label) : Prop :=
  StepSoundOfRead gammaInterval lts read transfer

/-- Bridge from local interval-transition soundness to framework `SoundStep`. -/
theorem soundStep_postStep_interval_of_stepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : IntervalTransfer Label)
    (hStep : IntervalStepSound lts read transfer) :
    SoundStep (postStep lts) (gammaIntervalState read) transfer := by
  simpa [IntervalStepSound, gammaIntervalState] using
    (soundStep_postStep_of_stepSound (gamma := gammaInterval) lts read transfer hStep)

/-- Build an LTS abstraction from local interval-step soundness obligations. -/
def intervalAbstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : IntervalTransfer Label)
    (hStep : IntervalStepSound lts read transfer) :
    LTSAbstraction State Label Interval :=
  abstractionOfStepSound (gamma := gammaInterval) lts read transfer hStep

end Analyses
end LTS
end Instances
end AbsInterpLTS
