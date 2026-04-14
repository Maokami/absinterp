import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.HasTau

import AbsInterp.Framework.Semantics.Weak
import AbsInterp.Instances.LTS.Semantics.Concrete
import AbsInterp.Instances.LTS.Semantics.Collecting

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v

/-!
# Weak Semantics for LTS

Weak (saturated) post operators wrapping CSLib's `STr` / `saturate` /
`τClosure`.  The core insight is that weak semantics is strong semantics
on the saturated LTS.
-/

section WeakPost

variable
    {State : Type u}
    {Label : Type v}
    [HasTau Label]

/-- One-step weak post via `lts.STr` (τ* · μ · τ*). -/
def weakPostStep
    (lts : Cslib.LTS State Label)
    (label : Label) :
    Post State :=
  postStep lts.saturate label

/-- Unlabeled weak collecting post (union over all labels of weak step). -/
def weakPostAny
    (lts : Cslib.LTS State Label) :
    Post State :=
  postAny lts.saturate

/-- Pack weak collecting into a framework `CollectingStep`. -/
def weakPostAny_collectingStep
    (lts : Cslib.LTS State Label) :
    CollectingStep State :=
  postAny_collectingStep lts.saturate

/-- Weak post equals strong post on the saturated LTS. -/
theorem weakPostStep_eq_postStep_saturate
    (lts : Cslib.LTS State Label)
    (label : Label) :
    weakPostStep lts label = postStep lts.saturate label :=
  rfl

/--
Every strong transition is a weak transition:
`postStep lts label ⊆ weakPostStep lts label`.
-/
theorem postStep_subset_weakPostStep
    (lts : Cslib.LTS State Label)
    (label : Label)
    (states : Set State) :
    postStep lts label states ⊆ weakPostStep lts label states := by
  intro s' hs'
  simp only [postStep] at hs'
  simp only [weakPostStep, postStep]
  rw [Cslib.LTS.mem_setImage] at hs' ⊢
  obtain ⟨s, hsMem, htr⟩ := hs'
  exact ⟨s, hsMem, Cslib.LTS.STr.single lts htr⟩

/--
Every strong unlabeled post is contained in the weak unlabeled post:
`postAny lts ⊆ weakPostAny lts`.
-/
theorem postAny_subset_weakPostAny
    (lts : Cslib.LTS State Label)
    (states : Set State) :
    postAny lts states ⊆ weakPostAny lts states := by
  intro s' hs'
  simp only [postAny, weakPostAny] at hs' ⊢
  obtain ⟨label, hlabel⟩ := hs'
  exact ⟨label, postStep_subset_weakPostStep lts label states hlabel⟩

end WeakPost

section TauClosure

variable
    {State : Type u}
    {Label : Type v}
    [HasTau Label]

/-- Membership in τ-closure: `s' ∈ τClosure lts S ↔ ∃ s ∈ S, lts.STr s τ s'`. -/
theorem mem_tauClosure
    (lts : Cslib.LTS State Label)
    (S : Set State)
    (s' : State) :
    s' ∈ lts.τClosure S ↔ ∃ s ∈ S, lts.STr s HasTau.τ s' := by
  simp only [Cslib.LTS.τClosure]
  rw [Cslib.LTS.mem_setImage]
  simp only [Cslib.LTS.saturate]

/-- τ-closure as a framework `ClosureOp`. -/
def tauClosureOp
    (lts : Cslib.LTS State Label) :
    ClosureOp State where
  cl := lts.τClosure
  extensive := by
    intro S s hs
    rw [mem_tauClosure]
    exact ⟨s, hs, Cslib.LTS.STr.refl⟩
  monotone := by
    intro S T hSub s' hs'
    rw [mem_tauClosure] at hs' ⊢
    obtain ⟨s, hsMem, hstr⟩ := hs'
    exact ⟨s, hSub hsMem, hstr⟩
  idempotent := by
    intro S
    ext s'
    constructor
    · intro hs'
      rw [mem_tauClosure] at hs'
      obtain ⟨s, hsMem, hstr2⟩ := hs'
      rw [mem_tauClosure] at hsMem
      obtain ⟨s₀, hs₀, hstr1⟩ := hsMem
      rw [mem_tauClosure]
      exact ⟨s₀, hs₀, Cslib.LTS.STr.trans_τ lts hstr1 hstr2⟩
    · intro hs'
      obtain ⟨s, hsMem, hstr⟩ := (mem_tauClosure lts S s').mp hs'
      apply (mem_tauClosure lts (lts.τClosure S) s').mpr
      exact ⟨s, (mem_tauClosure lts S s).mpr ⟨s, hsMem, Cslib.LTS.STr.refl⟩, hstr⟩

end TauClosure

end LTS
end Instances
end AbsInterp
