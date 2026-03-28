import Cslib.Init

import AbsInterp.Framework.Soundness
import AbsInterp.Instances.LTS.Semantics.Concrete

namespace AbsInterp
namespace Instances
namespace LTS

open AbsInterp.Framework

universe u v w

/--
Reusable explicit interface for one-step abstract interpretation over CSLib LTS.
-/
structure LTSAbstraction
    (State : Type u)
    (Label : Type v)
    (Abstract : Type w) where
  lts : Cslib.LTS State Label
  gamma : Gamma Abstract State
  transfer : StepPostSharp Abstract Label
  soundStep : SoundStep (postStep lts) gamma transfer

/-- Convenience constructor with explicit data. -/
def LTSAbstraction.ofExplicit
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (lts : Cslib.LTS State Label)
    (gamma : Gamma Abstract State)
    (transfer : StepPostSharp Abstract Label)
    (soundStep : SoundStep (postStep lts) gamma transfer) :
    LTSAbstraction State Label Abstract :=
  {
    lts := lts
    gamma := gamma
    transfer := transfer
    soundStep := soundStep
  }

end LTS
end Instances
end AbsInterp
