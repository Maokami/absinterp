import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterp.Framework.Soundness
import AbsInterp.Framework.Domains.Concretization
import AbsInterp.Instances.LTS.Semantics.Concrete
import AbsInterp.Instances.LTS.Semantics.Collecting
import AbsInterp.Instances.LTS.Instantiation.Interface
import AbsInterp.Instances.LTS.Instantiation.CollectingInterface

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
  (State -> Observation) -> Concretization Abstract State

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

/-!
## Readout-based collecting soundness

Parallel readout path for the unlabeled collecting abstraction, used to
discharge `LTSCollectingAbstraction.soundAny` for domains that observe
states through a readout function. This mirrors `StepSoundOfRead` /
`abstractionOfStepSound` on the labeled trace side.
-/

/--
Local unlabeled collecting soundness condition for readout-based
abstract LTS analyses.

Any transition `s →? s'` from a state in `γ(a)` lands in `γ(transferAny a)`,
independently of the label used.
-/
def CollectingSoundOfRead
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    (gamma : Abstract -> Set Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transferAny : PostSharp Abstract) : Prop :=
  ∀ (a : Abstract) (s s' : State),
    s ∈ gammaStateOfRead gamma read a ->
    (∃ label : Label, lts.Tr s label s') ->
    s' ∈ gammaStateOfRead gamma read (transferAny a)

/-- Bridge from local readout-based collecting soundness to framework `Sound`
over `postAny`. -/
theorem sound_postAny_of_collectingSound
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    (gamma : Abstract -> Set Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transferAny : PostSharp Abstract)
    (hAny : CollectingSoundOfRead gamma lts read transferAny) :
    Sound (postAny lts) (gammaStateOfRead gamma read) transferAny := by
  intro a s' hs'
  rcases (mem_postAny (lts := lts)
      (states := gammaStateOfRead gamma read a) (s' := s')).1 hs'
    with ⟨s, hsMem, label, htr⟩
  exact hAny a s s' hsMem ⟨label, htr⟩

/-- Lift a γ-only concretization domain on observations to one on states
through a readout function. -/
def ConcretizationDomain.ofRead
    {State : Type u}
    {Abstract : Type w}
    {Observation : Type x}
    [Preorder Abstract] [OrderTop Abstract]
    (domain : AbsInterp.Framework.Domains.ConcretizationDomain Abstract Observation)
    (read : State -> Observation) :
    AbsInterp.Framework.Domains.ConcretizationDomain Abstract State where
  gamma := gammaStateOfRead domain.gamma read
  gamma_monotone := fun _ _ h _ hs => domain.gamma_monotone h hs
  gamma_top := fun s => domain.gamma_top (read s)

/-- Build an LTS collecting abstraction from local readout-based collecting
soundness obligations. -/
def collectingAbstractionOfCollectingSound
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {Observation : Type x}
    [SemilatticeSup Abstract] [OrderTop Abstract]
    (domain : AbsInterp.Framework.Domains.ConcretizationDomain Abstract Observation)
    (lts : Cslib.LTS State Label)
    (read : State -> Observation)
    (transferAny : PostSharp Abstract)
    (hAny : CollectingSoundOfRead domain.gamma lts read transferAny) :
    LTSCollectingAbstraction State Label Abstract where
  lts := lts
  domain := ConcretizationDomain.ofRead domain read
  transferAny := transferAny
  soundAny :=
    sound_postAny_of_collectingSound domain.gamma lts read transferAny hAny

end Analyses
end LTS
end Instances
end AbsInterp
