import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS.Framework.Semantics
import AbsInterpLTS.Instances.LTS.Semantics.Concrete

namespace AbsInterpLTS
namespace Instances
namespace LTS

open Cslib
open AbsInterpLTS.Framework

universe u v

/-- One-step unlabeled collecting post operator induced by an LTS. -/
def postAny
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    Post State :=
  fun states => { s' : State | ∃ label : Label, s' ∈ postStep lts label states }

@[simp] theorem mem_postAny
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {states : Set State}
    {s' : State} :
    s' ∈ postAny lts states ↔ ∃ s ∈ states, ∃ label : Label, lts.Tr s label s' := by
  constructor
  · intro hs
    rcases hs with ⟨label, hsLabel⟩
    rcases (Cslib.LTS.mem_setImage
      (lts := lts)
      (S := states)
      (μ := label)
      (s' := s')).1 (by simpa [postStep] using hsLabel) with ⟨s, hsMem, htr⟩
    exact ⟨s, hsMem, label, htr⟩
  · intro hs
    rcases hs with ⟨s, hsMem, label, htr⟩
    refine ⟨label, ?_⟩
    exact
      (Cslib.LTS.mem_setImage
        (lts := lts)
        (S := states)
        (μ := label)
        (s' := s')).2 ⟨s, hsMem, htr⟩

theorem tr_mem_postAny
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {states : Set State}
    {s s' : State}
    {label : Label}
    (hs : s ∈ states)
    (htr : lts.Tr s label s') :
    s' ∈ postAny lts states := by
  refine ⟨label, ?_⟩
  exact
    (Cslib.LTS.mem_setImage
      (lts := lts)
      (S := states)
      (μ := label)
      (s' := s')).2 ⟨s, hs, htr⟩

/-- Every labeled post-image is contained in the unlabeled collecting post. -/
theorem postStep_subset_postAny
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (label : Label)
    (states : Set State) :
    postStep lts label states ⊆ postAny lts states := by
  intro s' hs'
  exact ⟨label, hs'⟩

theorem postAny_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    MonotonePost (postAny lts) := by
  intro states states' hSubset s' hs'
  rcases hs' with ⟨label, hsLabel⟩
  rcases (Cslib.LTS.mem_setImage
    (lts := lts)
    (S := states)
    (μ := label)
    (s' := s')).1 (by simpa [postStep] using hsLabel) with ⟨s, hsMem, htr⟩
  refine ⟨label, ?_⟩
  exact
    (Cslib.LTS.mem_setImage
      (lts := lts)
      (S := states')
      (μ := label)
      (s' := s')).2 ⟨s, hSubset hsMem, htr⟩

/-- Pack unlabeled LTS collecting semantics as a framework `CollectingStep`. -/
def postAny_collectingStep
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    CollectingStep State where
  post := postAny lts
  monotone := postAny_monotone lts

theorem mem_postAny_iff_exists_mem_setImage
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {states : Set State}
    {s' : State} :
    s' ∈ postAny lts states ↔ ∃ label : Label, s' ∈ lts.setImage states label := by
  simp [postAny, postStep]

@[simp] theorem mem_postAny_singleton_iff
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {s s' : State} :
    s' ∈ postAny lts ({s} : Set State) ↔ ∃ label : Label, lts.Tr s label s' := by
  simp [postAny, postStep, Cslib.LTS.mem_setImage]

theorem canReach_of_mem_postAny_singleton
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {s s' : State}
    (hMem : s' ∈ postAny lts ({s} : Set State)) :
    lts.CanReach s s' := by
  rcases (mem_postAny_singleton_iff (lts := lts) (s := s) (s' := s')).1 hMem with
    ⟨label, htr⟩
  exact ⟨[label], Cslib.LTS.MTr.single (lts := lts) htr⟩

theorem postAny_reachF_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (init : Set State) :
    MonotonePost ((postAny_collectingStep lts).reachF init) :=
  (postAny_collectingStep lts).reachF_monotone init

end LTS
end Instances
end AbsInterpLTS
