import Cslib.Init

import AbsInterp.Framework.Semantics.Concrete.Defs

namespace AbsInterp
namespace Framework

universe u v

section Basic

/-- The identity concrete transformer is monotone. -/
theorem MonotonePost.id
    {State : Type u} :
    MonotonePost (fun states : Set State => states) := by
  intro s t hSubset
  exact hSubset

/-- Composition of monotone concrete transformers is monotone. -/
theorem MonotonePost.compose
    {State : Type u}
    {post1 post2 : Post State}
    (h1 : MonotonePost post1)
    (h2 : MonotonePost post2) :
    MonotonePost (composePost post1 post2) := by
  intro s t hSubset
  exact h2 (h1 hSubset)

end Basic

section Trace

theorem composePost_assoc
    {State : Type u}
    (post1 post2 post3 : Post State) :
    composePost (composePost post1 post2) post3 =
      composePost post1 (composePost post2 post3) := by
  funext states
  rfl

private theorem foldl_composePost_acc
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State) :
    ∀ (labels : List Label) (acc post0 : Post State),
      List.foldl
        (fun current label => composePost current (stepPost label))
        (composePost acc post0)
        labels =
          composePost
            acc
            (List.foldl
              (fun current label => composePost current (stepPost label))
              post0
              labels)
  | [], acc, post0 => by
      simp
  | label :: labels, acc, post0 => by
      simp [List.foldl, foldl_composePost_acc, composePost_assoc]

/--
Base case of concrete trace lifting:
`liftTracePost stepPost []` is the identity transformer.
-/
@[simp] theorem liftTracePost_nil
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State) :
    liftTracePost stepPost [] = (fun states : Set State => states) :=
  rfl

/--
Unfold trace lifting on a non-empty label list.

`liftTracePost stepPost (label :: labels)`
is one concrete step followed by the lifted remainder:
`composePost (stepPost label) (liftTracePost stepPost labels)`.
-/
@[simp] theorem liftTracePost_cons
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State)
    (label : Label)
    (labels : List Label) :
    liftTracePost stepPost (label :: labels) =
      composePost (stepPost label) (liftTracePost stepPost labels) := by
  have hacc :=
    foldl_composePost_acc
      (stepPost := stepPost)
      labels
      (stepPost label)
      (fun states : Set State => states)
  simpa [liftTracePost, liftTrace, List.foldl] using hacc

theorem liftTracePost_monotone_of_pointwise
    {State : Type u}
    {Label : Type v}
    {stepPost : Label -> Post State}
    (hStepMono : ∀ label : Label, MonotonePost (stepPost label)) :
    ∀ labels : List Label, MonotonePost (liftTracePost stepPost labels) := by
  intro labels
  induction labels with
  | nil =>
      intro s t hSubset
      simpa [liftTracePost_nil] using hSubset
  | cons label labels ih =>
      intro s t hSubset
      simpa [liftTracePost_cons] using
        (MonotonePost.compose
          (h1 := hStepMono label)
          (h2 := ih)
          hSubset)

/--
Trace lifting distributes over list append via `composePost`.
-/
theorem liftTracePost_append
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State)
    (ls1 ls2 : List Label) :
    liftTracePost stepPost (ls1 ++ ls2) =
      composePost (liftTracePost stepPost ls1) (liftTracePost stepPost ls2) := by
  induction ls1 with
  | nil =>
      ext states
      simp [composePost]
  | cons l ls1 ih =>
      simp [liftTracePost_cons, ih, composePost_assoc]

/--
Trace lifting with a single label appended applies that step last.
-/
theorem liftTracePost_snoc_apply
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State)
    (labels : List Label)
    (l : Label)
    (init : Set State) :
    liftTracePost stepPost (labels ++ [l]) init =
      stepPost l (liftTracePost stepPost labels init) := by
  simp [liftTracePost_append, composePost]

end Trace

end Framework
end AbsInterp
