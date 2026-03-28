import Cslib.Init

import AbsInterp.Framework.Semantics.Abstract.Defs

namespace AbsInterp
namespace Framework

universe u v

section Trace

private theorem composePostSharp_assoc
    {Abstract : Type u}
    (postSharp1 postSharp2 postSharp3 : PostSharp Abstract) :
    composePostSharp (composePostSharp postSharp1 postSharp2) postSharp3 =
      composePostSharp postSharp1 (composePostSharp postSharp2 postSharp3) := by
  funext a
  rfl

private theorem foldl_composePostSharp_acc
    {Abstract : Type u}
    {Label : Type v}
    (stepPostSharp : StepPostSharp Abstract Label) :
    ∀ (labels : List Label) (acc post0 : PostSharp Abstract),
      List.foldl
        (fun current label => composePostSharp current (stepPostSharp label))
        (composePostSharp acc post0)
        labels =
          composePostSharp
            acc
            (List.foldl
              (fun current label => composePostSharp current (stepPostSharp label))
              post0
              labels)
  | [], acc, post0 => by
      simp
  | label :: labels, acc, post0 => by
      simp [List.foldl, foldl_composePostSharp_acc, composePostSharp_assoc]

/--
Base case of abstract trace lifting:
`liftTracePostSharp stepPostSharp []` is the identity abstract transformer.
-/
@[simp] theorem liftTracePostSharp_nil
    {Abstract : Type u}
    {Label : Type v}
    (stepPostSharp : StepPostSharp Abstract Label) :
    liftTracePostSharp stepPostSharp [] = (fun a : Abstract => a) :=
  rfl

/--
Unfold abstract trace lifting on a non-empty label list.

`liftTracePostSharp stepPostSharp (label :: labels)`
is one abstract step followed by the lifted remainder:
`composePostSharp (stepPostSharp label) (liftTracePostSharp stepPostSharp labels)`.
-/
@[simp] theorem liftTracePostSharp_cons
    {Abstract : Type u}
    {Label : Type v}
    (stepPostSharp : StepPostSharp Abstract Label)
    (label : Label)
    (labels : List Label) :
    liftTracePostSharp stepPostSharp (label :: labels) =
      composePostSharp (stepPostSharp label) (liftTracePostSharp stepPostSharp labels) := by
  have hacc :=
    foldl_composePostSharp_acc
      (stepPostSharp := stepPostSharp)
      labels
      (stepPostSharp label)
      (fun a : Abstract => a)
  simpa [liftTracePostSharp, liftTrace, List.foldl] using hacc

end Trace

end Framework
end AbsInterp
