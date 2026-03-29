import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Semantics.Concrete.Collecting
import AbsInterp.Framework.Iteration.Collecting

namespace AbsInterp
namespace Framework

universe u

/-!
# Omega-Trace Interfaces

Generic ω-execution (infinite execution) concepts over the framework's
collecting semantics.  These definitions are LTS-library-agnostic;
the Instances layer connects them to CSLib's `ωTr`.

The headline result shape is: every ω-reachable state appears in some
finite Kleene iterate, so finite collecting already subsumes ω-reachability
for safety properties.
-/

/--
An infinite execution with respect to a collecting step: an infinite
sequence `exec : Nat → State` where each successor is in the
post-image of its predecessor.
-/
def IsOmegaExec
    {State : Type u}
    (cfg : CollectingStep State)
    (exec : Nat → State) : Prop :=
  ∀ n, exec (n + 1) ∈ cfg.post {exec n}

/--
States that appear on some infinite execution starting from `init`.
-/
def omegaReachable
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) : Set State :=
  { s | ∃ exec : Nat → State,
        exec 0 ∈ init ∧
        IsOmegaExec cfg exec ∧
        ∃ n, exec n = s }

/--
Helper: an ω-execution prefix of length `n` from `init` lands in
`kleeneNat init (n + 1)`.
-/
theorem omegaExec_mem_kleeneNat
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State)
    (exec : Nat → State)
    (hInit : exec 0 ∈ init)
    (hExec : IsOmegaExec cfg exec) :
    ∀ n, exec n ∈ cfg.kleeneNat init (n + 1) := by
  intro n
  induction n with
  | zero =>
    simp [CollectingStep.kleeneNat_succ]
    exact Or.inl hInit
  | succ n ih =>
    simp [CollectingStep.kleeneNat_succ]
    right
    exact cfg.monotone (Set.singleton_subset_iff.mpr ih) (hExec n)

/--
Every state on an infinite execution from `init` is in some Kleene iterate.

This is the fundamental safety-subsumption result: finite collecting
already captures every ω-reachable state.
-/
theorem omegaReachable_subset_iUnion_kleeneNat
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) :
    omegaReachable cfg init ⊆ ⋃ n, cfg.kleeneNat init n := by
  rintro s ⟨exec, hInit, hExec, n, rfl⟩
  exact Set.mem_iUnion.mpr ⟨n + 1, omegaExec_mem_kleeneNat cfg init exec hInit hExec n⟩

end Framework
end AbsInterp
