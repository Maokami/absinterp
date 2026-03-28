import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterp.Framework.Soundness
import AbsInterp.Instances.LTS.Semantics.Concrete
import AbsInterp.Instances.LTS.Instantiation.Interface

namespace AbsInterp
namespace Instances
namespace LTS
namespace Analyses

open AbsInterp.Framework

universe u v w x

/-- State concretization via an observation function into a domain concretization. -/
abbrev ReadGamma
    (Abstract : Type u)
    (Observation : Type v)
    (State : Type w) :=
  (State -> Observation) -> Gamma Abstract State

/-- Lift a concretization through a state observation function. -/
def gammaStateOfRead
    {Abstract : Type u}
    {Observation : Type v}
    {State : Type w}
    (gamma : Abstract -> Set Observation) :
    ReadGamma Abstract Observation State :=
  fun read a => { s : State | read s ∈ gamma a }

@[simp] theorem mem_gammaStateOfRead
    {Abstract : Type u}
    {Observation : Type v}
    {State : Type w}
    {gamma : Abstract -> Set Observation}
    {read : State -> Observation}
    {a : Abstract}
    {s : State} :
    s ∈ gammaStateOfRead gamma read a ↔ read s ∈ gamma a :=
  Iff.rfl

/--
Local one-step soundness condition for readout-based abstract LTS analyses.

This can be discharged by language-specific transition/transfer lemmas, then
lifted to framework `SoundStep`.
-/
def StepSoundOfRead
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    (gamma : Abstract -> Set Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transfer : StepPostSharp Abstract Label) : Prop :=
  ∀ (label : Label) (a : Abstract) (s s' : State),
    s ∈ gammaStateOfRead gamma read a ->
    lts.Tr s label s' ->
    s' ∈ gammaStateOfRead gamma read (transfer label a)

/-- Bridge from local readout-based soundness to framework `SoundStep`. -/
theorem soundStep_postStep_of_stepSound
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    (gamma : Abstract -> Set Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transfer : StepPostSharp Abstract Label)
    (hStep : StepSoundOfRead gamma lts read transfer) :
    SoundStep (postStep lts) (gammaStateOfRead gamma read) transfer := by
  intro label a s' hs'
  rcases (Cslib.LTS.mem_setImage
    (lts := lts)
    (S := gammaStateOfRead gamma read a)
    (μ := label)
    (s' := s')).1 (by simpa [postStep] using hs') with ⟨s, hsMem, htr⟩
  exact hStep label a s s' hsMem htr

/-- Build an LTS abstraction from local readout-based soundness obligations. -/
def abstractionOfStepSound
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    (gamma : Abstract -> Set Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transfer : StepPostSharp Abstract Label)
    (hStep : StepSoundOfRead gamma lts read transfer) :
    LTSAbstraction State Label Abstract :=
  LTSAbstraction.ofExplicit
    lts
    (gammaStateOfRead gamma read)
    transfer
    (soundStep_postStep_of_stepSound gamma lts read transfer hStep)

end Analyses
end LTS
end Instances
end AbsInterp
