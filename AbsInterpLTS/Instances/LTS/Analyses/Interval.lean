import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS.Domains.Interval
import AbsInterpLTS.Framework.Soundness
import AbsInterpLTS.Instances.LTS.Semantics.Concrete
import AbsInterpLTS.Instances.LTS.Instantiation.Interface

namespace AbsInterpLTS
namespace Instances
namespace LTS
namespace Analyses

open AbsInterpLTS.Framework
open AbsInterpLTS.Domains

universe u v

/-- State concretization for the interval domain via an integer observation function. -/
abbrev IntervalGamma (State : Type u) := (State -> Int) -> Gamma Interval State

/-- Lift `gammaInterval` to concrete states using a readout `State -> Int`. -/
def gammaIntervalState
    {State : Type u} :
    IntervalGamma State :=
  fun read a => { s : State | read s ∈ gammaInterval a }

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
  ∀ (label : Label) (a : Interval) (s s' : State),
    s ∈ gammaIntervalState read a ->
    lts.Tr s label s' ->
    s' ∈ gammaIntervalState read (transfer label a)

/-- Bridge from local interval-transition soundness to framework `SoundStep`. -/
theorem soundStep_postStep_interval_of_stepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : IntervalTransfer Label)
    (hStep : IntervalStepSound lts read transfer) :
    SoundStep (postStep lts) (gammaIntervalState read) transfer := by
  intro label a s' hs'
  rcases (Cslib.LTS.mem_setImage
    (lts := lts)
    (S := gammaIntervalState read a)
    (μ := label)
    (s' := s')).1 (by simpa [postStep] using hs') with ⟨s, hsMem, htr⟩
  exact hStep label a s s' hsMem htr

/-- Build an LTS abstraction from local interval-step soundness obligations. -/
def intervalAbstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : IntervalTransfer Label)
    (hStep : IntervalStepSound lts read transfer) :
    LTSAbstraction State Label Interval where
  lts := lts
  gamma := gammaIntervalState read
  transfer := transfer
  soundStep := soundStep_postStep_interval_of_stepSound lts read transfer hStep

end Analyses
end LTS
end Instances
end AbsInterpLTS
