import Cslib.Init
import Cslib.Foundations.Semantics.LTS.HasTau

import AbsInterp.Framework.Semantics.Weak
import AbsInterp.Framework.Soundness
import AbsInterp.Instances.LTS.Semantics.Weak
import AbsInterp.Instances.LTS.Semantics.Lemmas
import AbsInterp.Instances.LTS.Instantiation.Interface

/-!
# Weak (τ-closure) soundness for LTS abstractions

Bridges the LTS τ-closure operator `tauClosureOp` into the framework's
closure-based weak soundness theorems (`sound_weak_of_sound_closure`).

Given strong one-step soundness over an LTS and a concretization that is closed
under τ-closure, weak step soundness — and, via `soundTrace_of_soundStep`, weak
trace soundness — follow with no extra reasoning.

This connects the τ-closure operator `tauClosureOp` to the framework's
closure-based weak soundness layer, which the LTS τ-closure primitives in
`Semantics/Weak.lean` were not previously wired into. Relating this
closure-based weak post (`cl ∘ post ∘ cl`) to the saturate-based `weakPostStep`
(`postStep lts.saturate`) is left as further work.
-/

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v w

variable
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    [HasTau Label]

/--
Weak (τ-closure) step soundness from strong step soundness over an LTS,
provided the concretization is closed under τ-closure.
-/
theorem soundStep_weakClosure_of_soundStep
    (lts : Cslib.LTS State Label)
    {gamma : Concretization Abstract State}
    {transfer : StepPostSharp Abstract Label}
    (hSound : SoundStep (postStep lts) gamma transfer)
    (hClosed : GammaClosed (tauClosureOp lts) gamma) :
    SoundStep
      (fun label => weakPost (tauClosureOp lts) (postStep lts label))
      gamma transfer :=
  soundStep_weak_of_soundStep_closure hSound
    (fun label => postStep_monotone lts label) hClosed

/--
End-to-end: an `LTSAbstraction` whose concretization is closed under τ-closure
is sound for the weak (τ-closure) lifted trace transformer.
-/
theorem LTSAbstraction.soundTraceWeak
    (cfg : LTSAbstraction State Label Abstract)
    (hClosed : GammaClosed (tauClosureOp cfg.lts) cfg.gamma) :
    SoundTrace
      (liftTracePost
        (fun label => weakPost (tauClosureOp cfg.lts) (postStep cfg.lts label)))
      cfg.gamma
      (liftTracePostSharp cfg.transfer) :=
  soundTrace_of_soundStep
    (soundStep_weakClosure_of_soundStep cfg.lts cfg.soundStep hClosed)
    (fun label => weakPost_monotone (postStep_monotone cfg.lts label))

end LTS
end Instances
end AbsInterp
