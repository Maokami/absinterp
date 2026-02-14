import Cslib.Init

import AbsInterpLTS.Framework.Soundness.Lemmas
import AbsInterpLTS.Framework.Semantics.Concrete
import AbsInterpLTS.Framework.Semantics.Abstract

namespace AbsInterpLTS
namespace Framework

universe u v w

/--
Step soundness lifts to trace soundness.

Assumptions:
- `hStep : ∀ label a, stepPost label (gamma a) ⊆ gamma (stepPostSharp label a)`
- `hStepMono : ∀ label, MonotonePost (stepPost label)`

Conclusion:
- `∀ labels a,
    liftTracePost stepPost labels (gamma a) ⊆
      gamma (liftTracePostSharp stepPostSharp labels a)`.

Monotonicity is required to transport soundness through sequential composition.
-/
theorem soundTrace_of_soundStep
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {stepPost : Label -> Post State}
    {gamma : Gamma Abstract State}
    {stepPostSharp : StepPostSharp Abstract Label}
    (hStep : SoundStep stepPost gamma stepPostSharp)
    (hStepMono : ∀ label : Label, MonotonePost (stepPost label)) :
    SoundTrace (liftTracePost stepPost) gamma (liftTracePostSharp stepPostSharp) := by
  intro labels
  induction labels with
  | nil =>
      intro a s hs
      simpa using hs
  | cons label labels ih =>
      have hStepSound : Sound (stepPost label) gamma (stepPostSharp label) :=
        hStep label
      have hTraceMono : MonotonePost (liftTracePost stepPost labels) :=
        liftTracePost_monotone_of_pointwise
          (stepPost := stepPost)
          (hStepMono := hStepMono)
          labels
      have hConsSound :
          Sound
            (composePost (stepPost label) (liftTracePost stepPost labels))
            gamma
            (composePostSharp (stepPostSharp label) (liftTracePostSharp stepPostSharp labels)) :=
        Sound.compose
          (post1 := stepPost label)
          (post2 := liftTracePost stepPost labels)
          (gamma := gamma)
          (postSharp1 := stepPostSharp label)
          (postSharp2 := liftTracePostSharp stepPostSharp labels)
          hStepSound
          ih
          hTraceMono
      intro a
      simpa using hConsSound a

end Framework
end AbsInterpLTS
