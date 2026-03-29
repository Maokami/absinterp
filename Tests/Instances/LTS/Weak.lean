import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSWeak

open Cslib
open AbsInterp.Framework
open AbsInterp.Instances.LTS

/-!
# Smoke tests: Weak / τ-aware semantics

Toy LTS with τ-transitions:
- States: `Nat`
- Labels: `ToyLabel` = `.tau | .a`
- Transitions: `0 →τ→ 1`, `1 →a→ 2`, `0 →a→ 3`
-/

inductive ToyLabel where
  | tau
  | a
  deriving DecidableEq, Repr

instance : HasTau ToyLabel where
  τ := .tau

def toyLTS : Cslib.LTS Nat ToyLabel where
  Tr s μ s' :=
    (s = 0 ∧ μ = .tau ∧ s' = 1) ∨
    (s = 1 ∧ μ = .a   ∧ s' = 2) ∨
    (s = 0 ∧ μ = .a   ∧ s' = 3)

-- Strong step: 0 →a→ 3
example : (3 : Nat) ∈ postStep toyLTS .a {0} := by
  show 3 ∈ toyLTS.setImage {0} .a
  exact (Cslib.LTS.mem_setImage).mpr ⟨0, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

-- Weak step: 0 ⇒a⇒ 2  (via τ* · a · τ*: 0 →τ→ 1 →a→ 2)
example : (2 : Nat) ∈ weakPostStep toyLTS .a {0} := by
  show 2 ∈ toyLTS.saturate.setImage {0} .a
  apply (Cslib.LTS.mem_setImage).mpr
  refine ⟨0, rfl, ?_⟩
  apply Cslib.LTS.STr.tr
  · apply Cslib.LTS.STr.tr Cslib.LTS.STr.refl
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Cslib.LTS.STr.refl
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Cslib.LTS.STr.refl

-- 2 is NOT reachable via strong step from {0} with label .a
example : (2 : Nat) ∉ postStep toyLTS .a {0} := by
  intro h
  change 2 ∈ toyLTS.setImage {0} .a at h
  obtain ⟨s, hs, htr⟩ := (Cslib.LTS.mem_setImage).mp h
  rcases hs with rfl
  rcases htr with ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨_, _, h⟩ <;> omega

-- Strong ⊆ weak instantiation
example : postStep toyLTS .a {0} ⊆ weakPostStep toyLTS .a {0} :=
  postStep_subset_weakPostStep toyLTS .a {0}

-- τ-closure: {0} τ-closes to include 1
example : (1 : Nat) ∈ toyLTS.τClosure {0} := by
  rw [mem_tauClosure]
  refine ⟨0, rfl, ?_⟩
  apply Cslib.LTS.STr.tr Cslib.LTS.STr.refl
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Cslib.LTS.STr.refl

-- τ-closure: 0 is in τ-closure of {0} (reflexivity)
example : (0 : Nat) ∈ toyLTS.τClosure {0} := by
  rw [mem_tauClosure]
  exact ⟨0, rfl, Cslib.LTS.STr.refl⟩

-- tauClosureOp instantiation compiles
example : ClosureOp Nat := tauClosureOp toyLTS

-- tauClosureOp extensiveness
example : ({0} : Set Nat) ⊆ (tauClosureOp toyLTS).cl {0} :=
  (tauClosureOp toyLTS).extensive {0}

-- weakPostAny_collectingStep instantiation compiles
example : CollectingStep Nat := weakPostAny_collectingStep toyLTS

end InstancesLTSWeak
end Tests
