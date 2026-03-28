import Cslib.Init

import AbsInterp.Framework.Semantics.Concrete
import AbsInterp.Instances.LTS.Semantics.Concrete

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v

private theorem foldl_postStep_eq_foldl_setImage
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    ∀ (labels : List Label) (acc : Post State) (states : Set State),
      (List.foldl
        (fun current label => composePost current (postStep lts label))
        acc
        labels) states =
        List.foldl lts.setImage (acc states) labels
  | [], acc, states => by
      simp
  | label :: labels, acc, states => by
      simpa [List.foldl, composePost, postStep] using
        (foldl_postStep_eq_foldl_setImage
          lts
          labels
          (composePost acc (postStep lts label))
          states)

private theorem liftTracePost_postStep_apply
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    ∀ (labels : List Label) (states : Set State),
      (liftTracePost (postStep lts) labels) states =
        List.foldl lts.setImage states labels
  | labels, states => by
      simpa [liftTracePost] using
        (foldl_postStep_eq_foldl_setImage lts labels (fun s => s) states)

theorem postTrace_eq_liftTracePost_postStep
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    postTrace lts = liftTracePost (postStep lts) := by
  funext labels
  funext states
  rw [postTrace, Cslib.LTS.setImageMultistep_foldl_setImage]
  exact (liftTracePost_postStep_apply lts labels states).symm

theorem postStep_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (label : Label) :
    MonotonePost (postStep lts label) := by
  intro states states' hSubset s' hs'
  rw [postStep, Cslib.LTS.mem_setImage] at hs' ⊢
  obtain ⟨s, hsMem, htr⟩ := hs'
  exact ⟨s, hSubset hsMem, htr⟩

theorem postTrace_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (labels : List Label) :
    MonotonePost (postTrace lts labels) := by
  rw [postTrace_eq_liftTracePost_postStep]
  exact
    (liftTracePost_monotone_of_pointwise
      (stepPost := postStep lts)
      (hStepMono := fun label => postStep_monotone lts label)
      labels)

end LTS
end Instances
end AbsInterp
