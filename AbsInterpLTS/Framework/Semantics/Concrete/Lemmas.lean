import Cslib.Init

import AbsInterpLTS.Framework.Semantics.Concrete.Defs

namespace AbsInterpLTS
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

section Hom

/-- Any `PostHom` is monotone as a plain concrete transformer. -/
theorem MonotonePost.ofPostHom
    {State : Type u}
    (post : PostHom State) :
    MonotonePost post.toFun := by
  intro s t hSubset
  exact post.monotone' hSubset

@[simp] theorem composePostHom_toPost
    {State : Type u}
    (post1 post2 : PostHom State) :
    (composePostHom post1 post2).toPost = composePost post1.toPost post2.toPost :=
  rfl

end Hom

section Trace

private theorem foldl_post_eq_foldl_postHom_of_monotone
    {State : Type u}
    {Label : Type v}
    {stepPost : Label -> Post State}
    (hStepMono : ∀ label : Label, MonotonePost (stepPost label)) :
    ∀ (labels : List Label) (acc : Post State) (accHom : PostHom State),
      acc = accHom.toPost ->
      List.foldl (fun current label => composePost current (stepPost label)) acc labels =
        (List.foldl
          (fun current label => composePostHom current ((stepPost label).toHom (hStepMono label)))
          accHom
          labels).toPost
  | [], acc, accHom, hAcc => by
      simpa using hAcc
  | label :: labels, acc, accHom, hAcc => by
      have hAcc' :
          composePost acc (stepPost label) =
            (composePostHom accHom ((stepPost label).toHom (hStepMono label))).toPost := by
        ext states
        simp [composePost, composePostHom, PostHom.toPost, Post.toHom, hAcc, OrderHom.comp]
      simpa [List.foldl] using
        (foldl_post_eq_foldl_postHom_of_monotone
          (hStepMono := hStepMono)
          labels
          (composePost acc (stepPost label))
          (composePostHom accHom ((stepPost label).toHom (hStepMono label)))
          hAcc')

theorem liftTracePost_eq_liftTracePostHom_of_pointwise_monotone
    {State : Type u}
    {Label : Type v}
    {stepPost : Label -> Post State}
    (hStepMono : ∀ label : Label, MonotonePost (stepPost label)) :
    liftTracePost stepPost =
      fun labels =>
        (liftTracePostHom
          (fun label => (stepPost label).toHom (hStepMono label))
          labels).toPost := by
  funext labels
  simpa [liftTracePost, liftTracePostHom] using
    (foldl_post_eq_foldl_postHom_of_monotone
      (hStepMono := hStepMono)
      labels
      (fun states => states)
      OrderHom.id
      rfl)

theorem liftTracePost_monotone_of_postHom
    {State : Type u}
    {Label : Type v}
    {stepPost : StepPostHom State Label} :
    ∀ labels : List Label, MonotonePost (fun states => (liftTracePostHom stepPost labels).toPost states) := by
  intro labels
  exact MonotonePost.ofPostHom (liftTracePostHom stepPost labels)

theorem liftTracePost_monotone_of_pointwise
    {State : Type u}
    {Label : Type v}
    {stepPost : Label -> Post State}
    (hStepMono : ∀ label : Label, MonotonePost (stepPost label)) :
    ∀ labels : List Label, MonotonePost (liftTracePost stepPost labels) := by
  let stepPostHom : StepPostHom State Label :=
    fun label => (stepPost label).toHom (hStepMono label)
  have hEq :
      liftTracePost stepPost = fun labels => (liftTracePostHom stepPostHom labels).toPost :=
    liftTracePost_eq_liftTracePostHom_of_pointwise_monotone hStepMono
  simpa [hEq] using (liftTracePost_monotone_of_postHom (stepPost := stepPostHom))

end Trace

end Framework
end AbsInterpLTS
