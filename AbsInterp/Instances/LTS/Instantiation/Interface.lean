import Cslib.Init

import AbsInterp.Framework.Soundness.Defs
import AbsInterp.Instances.LTS.Semantics.Concrete

/-!
# LTS Abstraction Interface

`LTSAbstraction` is a reusable bundle that packages a CSLib LTS together with
an abstract domain and a step-sound transfer function, enabling uniform
trace-soundness proofs via `soundTrace_of_soundStep`.

## References

* X. Leroy, *Mechanizing abstract interpretation*,
  Workshop on the Next 40 years of Abstract Interpretation (N40AI), 2024.
  https://xavierleroy.org/talks/N40AI.pdf
* C. Barrett et al., *CSLib: The Lean Computer Science Library*,
  arXiv:2602.04846, 2026. https://github.com/leanprover/cslib
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
  gamma : Concretization Abstract State
  /-- The abstract transfer function (one step per label). -/
  transfer : StepPostSharp Abstract Label
  soundStep : SoundStep (postStep lts) gamma transfer

/-- Convenience constructor with explicit data. -/
def LTSAbstraction.ofExplicit
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    (lts : Cslib.LTS State Label)
    (gamma : Concretization Abstract State)
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
