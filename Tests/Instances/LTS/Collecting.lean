import Cslib.Init

import AbsInterpLTS

namespace Tests
namespace InstancesLTSCollecting

open AbsInterpLTS
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Iteration
open AbsInterpLTS.Instances.LTS

def toyLTS : Cslib.LTS Nat Bool where
  Tr s label s' :=
    (s = 0 ∧ label = false ∧ s' = 1) ∨
    (s = 0 ∧ label = true ∧ s' = 2) ∨
    (s = 2 ∧ label = false ∧ s' = 3)

abbrev postToy : Post Nat := postAny toyLTS

def initZero : Set Nat := {0}

abbrev collectingToy : CollectingStep Nat := postAny_collectingStep toyLTS

abbrev kleeneToy : Nat -> Set Nat := collectingToy.kleeneNat initZero

@[simp] theorem kleeneToy_zero : kleeneToy 0 = ∅ := by
  simp [kleeneToy, CollectingStep.kleeneNat_zero]

@[simp] theorem kleeneToy_succ (n : Nat) :
    kleeneToy (n + 1) = initZero ∪ postToy (kleeneToy n) := by
  simp [kleeneToy, CollectingStep.kleeneNat_succ, collectingToy, postAny_collectingStep, postToy]

theorem mem_postToy_from_zero_false : 1 ∈ postToy ({0} : Set Nat) := by
  exact tr_mem_postAny
    (lts := toyLTS)
    (states := ({0} : Set Nat))
    (s := 0)
    (label := false)
    (by simp)
    (Or.inl ⟨rfl, rfl, rfl⟩)

theorem mem_postToy_from_zero_true : 2 ∈ postToy ({0} : Set Nat) := by
  exact tr_mem_postAny
    (lts := toyLTS)
    (states := ({0} : Set Nat))
    (s := 0)
    (label := true)
    (by simp)
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

theorem not_mem_postToy_from_zero_three : 3 ∉ postToy ({0} : Set Nat) := by
  intro hMem
  rcases (mem_postAny (lts := toyLTS) (states := ({0} : Set Nat)) (s' := 3)).1 hMem with
    ⟨s, hs, label, htr⟩
  have hsZero : s = 0 := by simpa using hs
  subst hsZero
  cases label <;> simp [toyLTS] at htr

example (S T : Set Nat) (hST : S ⊆ T) : postToy S ⊆ postToy T := by
  exact postAny_monotone toyLTS hST

theorem postToy_empty : postToy (∅ : Set Nat) = (∅ : Set Nat) := by
  ext x
  constructor
  · intro hx
    rcases (mem_postAny
      (lts := toyLTS)
      (states := (∅ : Set Nat))
      (s' := x)).1 hx with ⟨s, hs, label, htr⟩
    simp at hs
  · intro hx
    simp at hx

theorem kleeneNat_one_eq_initZero :
    collectingToy.kleeneNat initZero 1 = initZero := by
  calc
    collectingToy.kleeneNat initZero 1
        = initZero ∪ postToy (kleeneToy 0) := by
            simpa [kleeneToy] using kleeneToy_succ 0
    _ = initZero := by
      simp [postToy_empty]

@[simp] theorem kleeneToy_one : kleeneToy 1 = initZero := by
  simpa [kleeneToy] using kleeneNat_one_eq_initZero

theorem mem_zero_kleeneNat_one : 0 ∈ collectingToy.kleeneNat initZero 1 := by
  rw [kleeneNat_one_eq_initZero]
  simp [initZero]

theorem mem_one_kleeneNat_two : 1 ∈ collectingToy.kleeneNat initZero 2 := by
  have hPost : 1 ∈ postToy initZero := by
    simpa [initZero] using mem_postToy_from_zero_false
  have hPostAtOne : 1 ∈ postToy (kleeneToy 1) := by
    rw [kleeneToy_one]
    exact hPost
  have hUnion : 1 ∈ initZero ∪ postToy (kleeneToy 1) := by
    exact Or.inr hPostAtOne
  have hk2 : collectingToy.kleeneNat initZero 2 = initZero ∪ postToy (kleeneToy 1) := by
    simpa [kleeneToy] using kleeneToy_succ 1
  rw [hk2]
  exact hUnion

theorem mem_two_kleeneNat_two : 2 ∈ collectingToy.kleeneNat initZero 2 := by
  have hPost : 2 ∈ postToy initZero := by
    simpa [initZero] using mem_postToy_from_zero_true
  have hPostAtOne : 2 ∈ postToy (kleeneToy 1) := by
    rw [kleeneToy_one]
    exact hPost
  have hUnion : 2 ∈ initZero ∪ postToy (kleeneToy 1) := by
    exact Or.inr hPostAtOne
  have hk2 : collectingToy.kleeneNat initZero 2 = initZero ∪ postToy (kleeneToy 1) := by
    simpa [kleeneToy] using kleeneToy_succ 1
  rw [hk2]
  exact hUnion

theorem mem_three_kleeneNat_three : 3 ∈ collectingToy.kleeneNat initZero 3 := by
  have hTwo : 2 ∈ collectingToy.kleeneNat initZero 2 := mem_two_kleeneNat_two
  have hPost : 3 ∈ postToy (kleeneToy 2) := by
    exact tr_mem_postAny
      (lts := toyLTS)
      (states := kleeneToy 2)
      (s := 2)
      (label := false)
      hTwo
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have hUnion : 3 ∈ initZero ∪ postToy (kleeneToy 2) := Or.inr hPost
  have hk3 : collectingToy.kleeneNat initZero 3 = initZero ∪ postToy (kleeneToy 2) := by
    simpa [kleeneToy] using kleeneToy_succ 2
  rw [hk3]
  exact hUnion

theorem not_mem_three_kleeneNat_two : 3 ∉ collectingToy.kleeneNat initZero 2 := by
  intro hThree
  have hk2 : collectingToy.kleeneNat initZero 2 = initZero ∪ postToy (kleeneToy 1) := by
    simpa [kleeneToy] using kleeneToy_succ 1
  have hThree' : 3 ∈ initZero ∪ postToy (kleeneToy 1) := by
    rw [← hk2]
    exact hThree
  rcases hThree' with hInit | hPost
  · simp [initZero] at hInit
  · have hPost' : 3 ∈ postToy initZero := by
      rw [kleeneToy_one] at hPost
      exact hPost
    have hNot : 3 ∉ postToy ({0} : Set Nat) := not_mem_postToy_from_zero_three
    exact hNot (by simpa [initZero] using hPost')

example : 0 ∈ collectingToy.kleeneNat initZero 1 := mem_zero_kleeneNat_one
example : 1 ∈ collectingToy.kleeneNat initZero 2 := mem_one_kleeneNat_two
example : 2 ∈ collectingToy.kleeneNat initZero 2 := mem_two_kleeneNat_two
example : 3 ∈ collectingToy.kleeneNat initZero 3 := mem_three_kleeneNat_three
example : 3 ∉ collectingToy.kleeneNat initZero 2 := not_mem_three_kleeneNat_two

example (x : Nat) (hx : x ∈ postToy ({0} : Set Nat)) :
    toyLTS.CanReach 0 x := by
  exact canReach_of_mem_postAny_singleton
    (lts := toyLTS)
    (s := 0)
    (s' := x)
    (by simpa [postToy] using hx)

example :
    MonotonePost (collectingToy.reachF initZero) := by
  exact postAny_reachF_monotone (lts := toyLTS) (init := initZero)

end InstancesLTSCollecting
end Tests
