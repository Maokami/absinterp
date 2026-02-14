import Cslib.Init

import AbsInterpLTS.Framework.Soundness
import AbsInterpLTS.Instances.LTS.Semantics.Lemmas
import AbsInterpLTS.Instances.LTS.Instantiation.Interface

namespace AbsInterpLTS
namespace Instances
namespace LTS

open AbsInterpLTS.Framework

universe u v w

/-- Trace soundness follows from `soundStep` via trace lifting. -/
theorem LTSAbstraction.soundTraceLifted
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (cfg : LTSAbstraction State Label Abstract) :
    SoundTrace
      (liftTracePost (postStep cfg.lts))
      cfg.gamma
      (liftTracePostSharp cfg.transfer) := by
  simpa using
    (soundTrace_of_soundStep
      (stepPost := postStep cfg.lts)
      (gamma := cfg.gamma)
      (stepPostSharp := cfg.transfer)
      cfg.soundStep
      (hStepMono := fun label => postStep_monotone cfg.lts label))

/-- Explicit-data corollary of trace soundness lifting, routed through `LTSAbstraction`. -/
theorem LTSAbstraction.soundTraceLiftedOfExplicit
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (lts : Cslib.LTS State Label)
    (gamma : Gamma Abstract State)
    (transfer : StepPostSharp Abstract Label)
    (soundStep : SoundStep (postStep lts) gamma transfer) :
    SoundTrace
      (liftTracePost (postStep lts))
      gamma
      (liftTracePostSharp transfer) := by
  exact
    (LTSAbstraction.ofExplicit
      (State := State)
      (Label := Label)
      (Abstract := Abstract)
      lts
      gamma
      transfer
      soundStep).soundTraceLifted

end LTS
end Instances
end AbsInterpLTS
