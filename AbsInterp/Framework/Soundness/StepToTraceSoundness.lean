import Cslib.Init

import AbsInterp.Framework.Soundness.Defs
import AbsInterp.Framework.Soundness.Lemmas
import AbsInterp.Framework.Semantics.Concrete.Lemmas
import AbsInterp.Framework.Semantics.Abstract.Lemmas

/-!
# From Step Soundness to Trace Soundness

The central lifting theorem `soundTrace_of_soundStep`: pointwise step soundness
implies trace soundness over arbitrary finite label sequences.

Monotonicity of each step's post-condition transformer is required to transport
soundness through sequential composition.

## References

* X. Leroy, *Semantics and Verification of Computer Programs*,
  MPRI lecture notes (N40AI), 2023–2024.
  (γ-only soundness propagation over trace semantics)
* P. Cousot, R. Cousot, *Abstract Interpretation: A Unified Lattice Model for
  Static Analysis of Programs by Construction or Approximation of Fixpoints*,
  POPL 1977. doi:10.1145/512950.512973
-/

namespace AbsInterp
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
    {gamma : Concretization Abstract State}
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
      intro a
      rw [liftTracePost_cons, liftTracePostSharp_cons]
      exact
        Sound.compose
          (post1 := stepPost label)
          (post2 := liftTracePost stepPost labels)
          (gamma := gamma)
          (postSharp1 := stepPostSharp label)
          (postSharp2 := liftTracePostSharp stepPostSharp labels)
          (hStep label)
          ih
          (liftTracePost_monotone_of_pointwise
            (stepPost := stepPost)
            (hStepMono := hStepMono)
            labels) a

end Framework
end AbsInterp
