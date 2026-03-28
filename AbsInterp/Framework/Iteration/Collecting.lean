import Cslib.Init

import AbsInterp.Framework.Semantics.Concrete.Collecting
import AbsInterp.Framework.Iteration.NatIter

namespace AbsInterp
namespace Framework

open AbsInterp.Framework

universe u

namespace CollectingStep

/--
Nat-indexed Kleene iteration for collecting semantics:
`X₀ = ∅`, `Xₙ₊₁ = init ∪ post Xₙ`.
-/
def kleeneNat
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) :
    Nat -> Set State :=
  Iteration.iterateNat (cfg.reachF init) ∅

@[simp] theorem kleeneNat_zero
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) :
    cfg.kleeneNat init 0 = ∅ :=
  rfl

@[simp] theorem kleeneNat_succ
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State)
    (n : Nat) :
    cfg.kleeneNat init (n + 1) = init ∪ cfg.post (cfg.kleeneNat init n) := by
  simp [CollectingStep.kleeneNat, CollectingStep.reachF]

/--
Successor-chain step for collecting Kleene iteration.
-/
theorem kleeneNat_chain_step
    {State : Type u}
    (cfg : CollectingStep State) :
    ∀ (n : Nat) (init : Set State),
      cfg.kleeneNat init n ⊆ cfg.kleeneNat init (n + 1)
  | 0, init => by
      simp
  | n + 1, init => by
      simpa [cfg.kleeneNat_succ] using
        (Set.union_subset_union
          (Set.Subset.refl init)
          (cfg.monotone (cfg.kleeneNat_chain_step n init)))

/--
Collecting Kleene iteration chain monotonicity along natural-number indices.
-/
theorem kleeneNat_chain_of_le
    {State : Type u}
    (cfg : CollectingStep State)
    {m n : Nat}
    (hLe : m ≤ n)
    (init : Set State) :
    cfg.kleeneNat init m ⊆ cfg.kleeneNat init n := by
  have hAdd :
      ∀ k : Nat, cfg.kleeneNat init m ⊆ cfg.kleeneNat init (m + k) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        exact Set.Subset.trans ih (cfg.kleeneNat_chain_step (m + k) init)
  rcases Nat.exists_eq_add_of_le hLe with ⟨k, hk⟩
  simpa [hk] using hAdd k

/--
Every successor Kleene iterate contains the initial states.
-/
theorem init_subset_kleeneNat_succ
    {State : Type u}
    (cfg : CollectingStep State) :
    ∀ (n : Nat) (init : Set State), init ⊆ cfg.kleeneNat init (n + 1)
  | n, init => by simp

end CollectingStep

end Framework
end AbsInterp
