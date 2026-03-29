import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Semantics.Omega
import AbsInterp.Instances.LTS.Semantics.Collecting

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v

/-!
# Omega-Trace Semantics for LTS

ω-trace (infinite execution) wrappers connecting CSLib's `ωTr` to the
framework's generic `omegaReachable`.  The headline bridge result is:
every state on a CSLib `ωTr` appears in some finite Kleene iterate.
-/

section OmegaReachable

variable
    {State : Type u}
    {Label : Type v}

/--
States that appear on some `ωTr` from `init`.
-/
def omegaReachableLTS
    (lts : Cslib.LTS State Label)
    (init : Set State) : Set State :=
  { s | ∃ (ss : Cslib.ωSequence State) (μs : Cslib.ωSequence Label),
        lts.ωTr ss μs ∧ ss 0 ∈ init ∧ ∃ n, ss n = s }

/--
Bridge: CSLib `ωTr`-reachability implies framework `omegaReachable`
(over `postAny_collectingStep`).
-/
theorem omegaReachableLTS_subset_omegaReachable
    (lts : Cslib.LTS State Label)
    (init : Set State) :
    omegaReachableLTS lts init ⊆
      omegaReachable (postAny_collectingStep lts) init := by
  intro s hs
  simp only [omegaReachableLTS, Set.mem_setOf_eq] at hs
  obtain ⟨ss, μs, hωTr, hInit, n, rfl⟩ := hs
  simp only [omegaReachable, Set.mem_setOf_eq]
  refine ⟨⇑ss, hInit, ?_, n, rfl⟩
  intro i
  change ss (i + 1) ∈ postAny lts {ss i}
  rw [mem_postAny]
  exact ⟨ss i, Set.mem_singleton _, μs i, hωTr i⟩

/--
Composed bridge: every state on a CSLib `ωTr` appears in some finite
Kleene iterate of the strong collecting semantics.
-/
theorem omegaReachableLTS_subset_iUnion_kleeneNat
    (lts : Cslib.LTS State Label)
    (init : Set State) :
    omegaReachableLTS lts init ⊆
      ⋃ n, (postAny_collectingStep lts).kleeneNat init n := by
  intro s hs
  exact omegaReachable_subset_iUnion_kleeneNat
    (postAny_collectingStep lts) init
    (omegaReachableLTS_subset_omegaReachable lts init hs)

end OmegaReachable

section Divergence

variable
    {State : Type u}
    {Label : Type v}
    [HasTau Label]

/--
States in `init` from which the LTS diverges (admits an infinite
all-τ execution).
-/
def divergentFrom
    (lts : Cslib.LTS State Label)
    (init : Set State) : Set State :=
  { s | s ∈ init ∧ lts.Divergent s }

/--
Divergent states are a subset of ω-reachable states.
-/
theorem divergentFrom_subset_omegaReachableLTS
    (lts : Cslib.LTS State Label)
    (init : Set State) :
    divergentFrom lts init ⊆ omegaReachableLTS lts init := by
  intro s hs
  simp only [divergentFrom, Set.mem_setOf_eq] at hs
  obtain ⟨hInit, ss, μs, hωTr, hss0, _hDiv⟩ := hs
  simp only [omegaReachableLTS, Set.mem_setOf_eq]
  refine ⟨ss, μs, hωTr, ?_, 0, hss0⟩
  rw [hss0]; exact hInit

end Divergence

end LTS
end Instances
end AbsInterp
