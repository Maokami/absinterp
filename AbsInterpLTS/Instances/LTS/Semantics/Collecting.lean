import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterpLTS.Framework.Iteration
import AbsInterpLTS.Instances.LTS.Semantics.Concrete

namespace AbsInterpLTS
namespace Instances
namespace LTS

open Cslib
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Iteration

universe u v

/-- One-step unlabeled collecting post operator induced by an LTS. -/
def postAny
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    Post State :=
  fun states => { s' : State | ∃ s ∈ states, ∃ label : Label, lts.Tr s label s' }

@[simp] theorem mem_postAny
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {states : Set State}
    {s' : State} :
    s' ∈ postAny lts states ↔ ∃ s ∈ states, ∃ label : Label, lts.Tr s label s' :=
  Iff.rfl

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
  exact ⟨s, hs, label, htr⟩

theorem postAny_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label) :
    MonotonePost (postAny lts) := by
  intro states states' hSubset s' hs'
  rcases hs' with ⟨s, hs, label, htr⟩
  exact ⟨s, hSubset hs, label, htr⟩

theorem mem_postAny_iff_exists_mem_setImage
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {states : Set State}
    {s' : State} :
    s' ∈ postAny lts states ↔ ∃ label : Label, s' ∈ lts.setImage states label := by
  constructor <;> intro hs
  · simpa [Cslib.LTS.mem_setImage, exists_comm, and_left_comm, and_assoc] using hs
  · simpa [Cslib.LTS.mem_setImage, exists_comm, and_left_comm, and_assoc] using hs

@[simp] theorem mem_postAny_singleton_iff
    {State : Type u}
    {Label : Type v}
    {lts : Cslib.LTS State Label}
    {s s' : State} :
    s' ∈ postAny lts ({s} : Set State) ↔ ∃ label : Label, lts.Tr s label s' := by
  simp [postAny]

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

theorem reachF_postAny_monotone
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)
    (init : Set State) :
    MonotonePost (reachF init (postAny lts)) :=
  reachF_monotone_of_post_monotone
    (init := init)
    (post := postAny lts)
    (postAny_monotone lts)

end LTS
end Instances
end AbsInterpLTS
