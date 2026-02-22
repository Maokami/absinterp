import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS.Domains.Sign
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

/-- State concretization for the sign domain via an integer observation function. -/
abbrev SignGamma (State : Type u) := (State -> Int) -> Gamma Sign State

/-- Lift `gammaSign` to concrete states using a readout `State -> Int`. -/
def gammaSignState
    {State : Type u} :
    SignGamma State :=
  fun read a => { s : State | read s ∈ gammaSign a }

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
  ∀ (label : Label) (a : Sign) (s s' : State),
    s ∈ gammaSignState read a ->
    lts.Tr s label s' ->
    s' ∈ gammaSignState read (transfer label a)

/-- Bridge from local sign-transition soundness to framework `SoundStep`. -/
theorem soundStep_postStep_sign_of_stepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : SignTransfer Label)
    (hStep : SignStepSound lts read transfer) :
    SoundStep (postStep lts) (gammaSignState read) transfer := by
  intro label a s' hs'
  rcases (Cslib.LTS.mem_setImage
    (lts := lts)
    (S := gammaSignState read a)
    (μ := label)
    (s' := s')).1 (by simpa [postStep] using hs') with ⟨s, hsMem, htr⟩
  exact hStep label a s s' hsMem htr

/-- Build an LTS abstraction from local sign-step soundness obligations. -/
def signAbstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (read : State -> Int)
    (transfer : SignTransfer Label)
    (hStep : SignStepSound lts read transfer) :
    LTSAbstraction State Label Sign where
  lts := lts
  gamma := gammaSignState read
  transfer := transfer
  soundStep := soundStep_postStep_sign_of_stepSound lts read transfer hStep

end Analyses
end LTS
end Instances
end AbsInterpLTS
