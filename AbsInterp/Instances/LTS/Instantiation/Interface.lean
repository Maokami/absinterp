import Cslib.Init

import AbsInterp.Framework.Soundness.Defs
import AbsInterp.Instances.LTS.Semantics.Concrete

/-!
# LTS Abstraction Interface

`LTSAbstraction` is a reusable bundle that packages a CSLib LTS together with
an abstract domain and a step-sound transfer function, enabling uniform
trace-soundness proofs via `soundTrace_of_soundStep`.

## References

* X. Leroy, *Semantics and Verification of Computer Programs*,
  MPRI lecture notes (N40AI), 2023–2024.
* R. Montesi et al., *CSLib: A Lean 4 Library for Computer Science Foundations*,
  leanprover/cslib, 2024–2025. https://github.com/leanprover/cslib
-/

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
  /-- The underlying CSLib LTS. -/
  lts : Cslib.LTS State Label
  /-- The concretization function mapping abstract elements to concrete state sets. -/
  gamma : Gamma Abstract State
  /-- The abstract transfer function (one step per label). -/
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
