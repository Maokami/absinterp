import Cslib.Init

import AbsInterpLTS.Framework.Soundness.Defs

namespace AbsInterpLTS
namespace Framework

universe u v w

/--
Step soundness implies trace soundness:
`(∀ label a, stepPost label (gamma a) ⊆ gamma (postAbs label a)) ->
 (∀ labels a, liftTracePost stepPost labels (gamma a) ⊆ gamma (liftTracePostSharp postAbs labels a))`.

This theorem is currently a staged proof obligation.
-/
theorem soundTrace_of_soundStep
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {stepPost : Label -> Post State}
    {gamma : Gamma Abstract State}
    {postAbs : StepPostSharp Abstract Label}
    (hStep : SoundStep stepPost gamma postAbs) :
    SoundTrace (liftTracePost stepPost) gamma (liftTracePostSharp postAbs) := by
  sorry

end Framework
end AbsInterpLTS
