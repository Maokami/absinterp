import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSCollectingTrace

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Instances.LTS

/-- Reuse the toyLTS from Collecting tests: 0 →false→ 1, 0 →true→ 2, 2 →false→ 3. -/
def toyLTS : Cslib.LTS Nat Bool where
  Tr s label s' :=
    (s = 0 ∧ label = false ∧ s' = 1) ∨
    (s = 0 ∧ label = true ∧ s' = 2) ∨
    (s = 2 ∧ label = false ∧ s' = 3)

abbrev collectingToy : CollectingStep Nat := postAny_collectingStep toyLTS

def initZero : Set Nat := {0}

abbrev kleeneToy : Nat -> Set Nat := collectingToy.kleeneNat initZero

/-! ## Theorem 1: traces are captured by collecting -/

/-- Trace `[false]` from `{0}` reaches `{1}`, which is in `kleeneToy 2`. -/
example : liftTracePost (postStep toyLTS) [false] initZero ⊆ kleeneToy 2 :=
  liftTracePost_subset_kleeneNat toyLTS [false] initZero 1 (by simp)

/-- Trace `[true, false]` from `{0}` is in `kleeneToy 3`. -/
example : liftTracePost (postStep toyLTS) [true, false] initZero ⊆ kleeneToy 3 :=
  liftTracePost_subset_kleeneNat toyLTS [true, false] initZero 2 (by simp)

/-! ## Theorem 2: collecting states have witness traces -/

/-- `3 ∈ kleeneToy 3` implies there is a witness trace of length ≤ 2. -/
example : ∃ labels : List Bool, labels.length ≤ 2 ∧
    (3 : Nat) ∈ liftTracePost (postStep toyLTS) labels initZero := by
  have h3 : (3 : Nat) ∈ kleeneToy 3 := by
    simp [CollectingStep.kleeneNat_succ, CollectingStep.kleeneNat_zero]
    right
    exact tr_mem_postAny
      (lts := toyLTS)
      (states := kleeneToy 2)
      (s := 2)
      (label := false)
      (by
        simp [CollectingStep.kleeneNat_succ, CollectingStep.kleeneNat_zero]
        right
        exact tr_mem_postAny
          (lts := toyLTS)
          (states := kleeneToy 1)
          (s := 0)
          (label := true)
          (by simp [CollectingStep.kleeneNat_succ, CollectingStep.kleeneNat_zero, initZero])
          (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  exact kleeneNat_subset_iUnion_liftTracePost toyLTS initZero 2 3 h3

/-! ## Theorem 3: equality instantiation -/

/-- Kleene chain at step 2 equals the union of traces of length ≤ 1. -/
example : kleeneToy 2 =
    ⋃ (labels : List Bool) (_ : labels.length ≤ 1),
      liftTracePost (postStep toyLTS) labels initZero :=
  kleeneNat_eq_iUnion_liftTracePost toyLTS initZero 1

end InstancesLTSCollectingTrace
end Tests
