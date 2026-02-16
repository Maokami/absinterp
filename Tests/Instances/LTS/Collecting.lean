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

theorem mem_postToy_from_zero_false : 1 ∈ postToy ({0} : Set Nat) := by
  exact ⟨0, by simp, false, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem mem_postToy_from_zero_true : 2 ∈ postToy ({0} : Set Nat) := by
  exact ⟨0, by simp, true, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩

theorem not_mem_postToy_from_zero_three : 3 ∉ postToy ({0} : Set Nat) := by
  intro hMem
  rcases (mem_postAny (lts := toyLTS) (states := ({0} : Set Nat)) (s' := 3)).1 hMem with
    ⟨s, hs, label, htr⟩
  have hsZero : s = 0 := by simpa using hs
  subst hsZero
  cases label <;> simp [toyLTS] at htr

example (S T : Set Nat) (hST : S ⊆ T) : postToy S ⊆ postToy T := by
  exact postAny_monotone toyLTS hST

theorem kleeneNat_one_eq_initZero :
    kleeneNat initZero postToy 1 = initZero := by
  ext x
  simp [kleeneNat_succ, kleeneNat_zero, postToy, postAny, initZero]

theorem mem_zero_kleeneNat_one : 0 ∈ kleeneNat initZero postToy 1 := by
  exact (init_subset_kleeneNat_succ (post := postToy) 0 initZero) (by simp [initZero])

theorem mem_one_kleeneNat_two : 1 ∈ kleeneNat initZero postToy 2 := by
  have hPost : 1 ∈ postToy initZero := by
    simpa [initZero] using mem_postToy_from_zero_false
  have hUnion : 1 ∈ initZero ∪ postToy (kleeneNat initZero postToy 1) := by
    exact Or.inr (by simpa [kleeneNat_one_eq_initZero] using hPost)
  simpa [kleeneNat_succ] using hUnion

theorem mem_two_kleeneNat_two : 2 ∈ kleeneNat initZero postToy 2 := by
  have hPost : 2 ∈ postToy initZero := by
    simpa [initZero] using mem_postToy_from_zero_true
  have hUnion : 2 ∈ initZero ∪ postToy (kleeneNat initZero postToy 1) := by
    exact Or.inr (by simpa [kleeneNat_one_eq_initZero] using hPost)
  simpa [kleeneNat_succ] using hUnion

theorem mem_three_kleeneNat_three : 3 ∈ kleeneNat initZero postToy 3 := by
  have hTwo : 2 ∈ kleeneNat initZero postToy 2 := mem_two_kleeneNat_two
  have hPost : 3 ∈ postToy (kleeneNat initZero postToy 2) := by
    exact tr_mem_postAny
      (lts := toyLTS)
      (states := kleeneNat initZero postToy 2)
      (s := 2)
      (label := false)
      hTwo
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have hUnion : 3 ∈ initZero ∪ postToy (kleeneNat initZero postToy 2) := Or.inr hPost
  simpa [kleeneNat_succ] using hUnion

theorem not_mem_three_kleeneNat_two : 3 ∉ kleeneNat initZero postToy 2 := by
  intro hThree
  have hThree' : 3 ∈ initZero ∪ postToy (kleeneNat initZero postToy 1) := by
    simpa [kleeneNat_succ] using hThree
  rcases hThree' with hInit | hPost
  · simp [initZero] at hInit
  · have hPost' : 3 ∈ postToy initZero := by
      simpa [kleeneNat_one_eq_initZero] using hPost
    have hNot : 3 ∉ postToy ({0} : Set Nat) := not_mem_postToy_from_zero_three
    exact hNot (by simpa [initZero] using hPost')

example : 0 ∈ kleeneNat initZero postToy 1 := mem_zero_kleeneNat_one
example : 1 ∈ kleeneNat initZero postToy 2 := mem_one_kleeneNat_two
example : 2 ∈ kleeneNat initZero postToy 2 := mem_two_kleeneNat_two
example : 3 ∈ kleeneNat initZero postToy 3 := mem_three_kleeneNat_three
example : 3 ∉ kleeneNat initZero postToy 2 := not_mem_three_kleeneNat_two

example (x : Nat) (hx : x ∈ postToy ({0} : Set Nat)) :
    toyLTS.CanReach 0 x := by
  exact canReach_of_mem_postAny_singleton
    (lts := toyLTS)
    (s := 0)
    (s' := x)
    (by simpa [postToy] using hx)

example :
    MonotonePost (reachF initZero postToy) := by
  change MonotonePost (reachF initZero (postAny toyLTS))
  exact reachF_postAny_monotone (lts := toyLTS) (init := initZero)

end InstancesLTSCollecting
end Tests
