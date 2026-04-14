import Cslib.Init
import Cslib.Foundations.Semantics.LTS.OmegaExecution
import Cslib.Foundations.Data.OmegaSequence.Defs

import AbsInterp

namespace Tests
namespace InstancesLTSOmega

open AbsInterp.Framework
open AbsInterp.Instances.LTS

/-!
# Smoke tests: ω-trace semantics

Toy looping LTS:
- States: `Nat`
- Labels: `Unit`
- Transitions: `0 →()→ 1`, `1 →()→ 0`
-/

def loopLTS : Cslib.LTS Nat Unit where
  Tr s _ s' :=
    (s = 0 ∧ s' = 1) ∨ (s = 1 ∧ s' = 0)

-- The alternating ω-sequence: 0, 1, 0, 1, ...
private def altStates : Cslib.ωSequence Nat where
  get n := if n % 2 = 0 then 0 else 1

private def constLabels : Cslib.ωSequence Unit where
  get _ := ()

-- altStates is a valid ω-execution of loopLTS
private theorem altStates_omegaExecution : loopLTS.OmegaExecution altStates constLabels := by
  intro i
  simp only [loopLTS, altStates, constLabels]
  by_cases h : i % 2 = 0
  · left
    refine ⟨?_, ?_⟩
    · simp [h]
    · have : (i + 1) % 2 = 1 := by omega
      simp [this]
  · right
    refine ⟨?_, ?_⟩
    · simp [h]
    · have : (i + 1) % 2 = 0 := by omega
      simp [this]

-- 0 is ω-reachable from {0}
example : (0 : Nat) ∈ omegaReachableLTS loopLTS {0} := by
  simp only [omegaReachableLTS, Set.mem_setOf_eq]
  exact ⟨altStates, constLabels, altStates_omegaExecution, rfl, 0, rfl⟩

-- 1 is ω-reachable from {0}
example : (1 : Nat) ∈ omegaReachableLTS loopLTS {0} := by
  simp only [omegaReachableLTS, Set.mem_setOf_eq]
  exact ⟨altStates, constLabels, altStates_omegaExecution, rfl, 1, rfl⟩

-- Bridge: ω-reachable ⊆ framework omegaReachable
example :
    omegaReachableLTS loopLTS {0} ⊆
      omegaReachable (postAny_collectingStep loopLTS) {0} :=
  omegaReachableLTS_subset_omegaReachable loopLTS {0}

-- Bridge: ω-reachable ⊆ ⋃ n, kleeneNat n
example :
    omegaReachableLTS loopLTS {0} ⊆
      ⋃ n, (postAny_collectingStep loopLTS).kleeneNat {0} n :=
  omegaReachableLTS_subset_iUnion_kleeneNat loopLTS {0}

-- Framework-level: IsOmegaExec instantiation
example : IsOmegaExec (postAny_collectingStep loopLTS) altStates := by
  intro i
  simp only [postAny_collectingStep, postAny, postStep, altStates, loopLTS]
  by_cases h : i % 2 = 0
  · refine ⟨(), ?_⟩
    rw [Cslib.LTS.mem_setImage]
    have hi1 : (i + 1) % 2 = 1 := by omega
    refine ⟨0, ?_, ?_⟩
    · simp [h]
    · left; simp [hi1]
  · refine ⟨(), ?_⟩
    rw [Cslib.LTS.mem_setImage]
    have hi1 : (i + 1) % 2 = 0 := by omega
    refine ⟨1, ?_, ?_⟩
    · simp [h]
    · right; simp [hi1]

end InstancesLTSOmega
end Tests
