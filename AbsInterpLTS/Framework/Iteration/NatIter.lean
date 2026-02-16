import Cslib.Init

import AbsInterpLTS.Framework.Semantics
import AbsInterpLTS.Framework.Soundness.Defs

namespace AbsInterpLTS
namespace Framework
namespace Iteration

open AbsInterpLTS.Framework

universe u

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

/--
Collecting-style fixpoint operator for reachability:
`reachF init post states = init ∪ post states`.
-/
def reachF
    {State : Type u}
    (init : Set State)
    (post : Post State) :
    Post State :=
  fun states => init ∪ post states

@[simp] theorem reachF_apply
    {State : Type u}
    (init : Set State)
    (post : Post State)
    (states : Set State) :
    reachF init post states = init ∪ post states :=
  rfl

theorem reachF_monotone_of_post_monotone
    {State : Type u}
    {init : Set State}
    {post : Post State}
    (hMono : MonotonePost post) :
    MonotonePost (reachF init post) := by
  intro states states' hSubset s hs
  rcases hs with hsInit | hsPost
  · exact Or.inl hsInit
  · exact Or.inr (hMono hSubset hsPost)

/-- Natural-number iterate scaffold for concrete next-step operators. -/
def iterateNat
    {State : Type u}
    (next : Post State)
    (init : Set State) :
    Nat -> Set State
  | 0 => init
  | n + 1 => next (iterateNat next init n)

/--
Nat-indexed Kleene iteration for collecting semantics:
`X₀ = ∅`, `Xₙ₊₁ = init ∪ post Xₙ`.
-/
def kleeneNat
    {State : Type u}
    (init : Set State)
    (post : Post State) :
    Nat -> Set State :=
  iterateNat (reachF init post) ∅

/-- Natural-number iterate scaffold for abstract next-step transformers. -/
def iterateNatSharp
    {Abstract : Type u}
    (nextSharp : PostSharp Abstract)
    (init : Abstract) :
    Nat -> Abstract
  | 0 => init
  | n + 1 => nextSharp (iterateNatSharp nextSharp init n)

@[simp] theorem iterateNat_zero
    {State : Type u}
    (next : Post State)
    (init : Set State) :
    iterateNat next init 0 = init :=
  rfl

@[simp] theorem iterateNat_succ
    {State : Type u}
    (next : Post State)
    (init : Set State)
    (n : Nat) :
    iterateNat next init (n + 1) = next (iterateNat next init n) :=
  rfl

@[simp] theorem iterateNatSharp_zero
    {Abstract : Type u}
    (nextSharp : PostSharp Abstract)
    (init : Abstract) :
    iterateNatSharp nextSharp init 0 = init :=
  rfl

@[simp] theorem iterateNatSharp_succ
    {Abstract : Type u}
    (nextSharp : PostSharp Abstract)
    (init : Abstract)
    (n : Nat) :
    iterateNatSharp nextSharp init (n + 1) =
      nextSharp (iterateNatSharp nextSharp init n) :=
  rfl

@[simp] theorem kleeneNat_zero
    {State : Type u}
    (init : Set State)
    (post : Post State) :
    kleeneNat init post 0 = ∅ :=
  rfl

@[simp] theorem kleeneNat_succ
    {State : Type u}
    (init : Set State)
    (post : Post State)
    (n : Nat) :
    kleeneNat init post (n + 1) = init ∪ post (kleeneNat init post n) := by
  simp [kleeneNat, reachF]

/--
Monotonicity of natural-number iteration in the initial set.

Assumptions:
- `hMono : MonotonePost next`
- `hInit : init1 ⊆ init2`

Conclusion:
- `iterateNat next init1 n ⊆ iterateNat next init2 n`.
-/
theorem iterateNat_monotone_init
    {State : Type u}
    {next : Post State}
    (hMono : MonotonePost next) :
    ∀ n : Nat, ∀ {init1 init2 : Set State},
      init1 ⊆ init2 ->
      iterateNat next init1 n ⊆ iterateNat next init2 n
  | 0, init1, init2, hInit => hInit
  | n + 1, init1, init2, hInit => by
      simpa using
        hMono (iterateNat_monotone_init (hMono := hMono) n hInit)

/--
Successor-chain step for collecting Kleene iteration.

Assumptions:
- `hMono : MonotonePost post`

Conclusion:
- `kleeneNat init post n ⊆ kleeneNat init post (n + 1)`.
-/
theorem kleeneNat_chain_step
    {State : Type u}
    {post : Post State}
    (hMono : MonotonePost post) :
    ∀ (n : Nat) (init : Set State),
      kleeneNat init post n ⊆ kleeneNat init post (n + 1)
  | 0, init => by
      simp
  | n + 1, init => by
      intro s hs
      simp [kleeneNat_succ] at hs ⊢
      rcases hs with hsInit | hsPost
      · exact Or.inl hsInit
      · exact Or.inr (hMono (kleeneNat_chain_step (hMono := hMono) n init) hsPost)

/--
Collecting Kleene iteration chain monotonicity along natural-number indices.

Assumptions:
- `hMono : MonotonePost post`
- `hLe : m ≤ n`

Conclusion:
- `kleeneNat init post m ⊆ kleeneNat init post n`.
-/
theorem kleeneNat_chain_of_le
    {State : Type u}
    {post : Post State}
    (hMono : MonotonePost post)
    {m n : Nat}
    (hLe : m ≤ n)
    (init : Set State) :
    kleeneNat init post m ⊆ kleeneNat init post n := by
  have hAdd :
      ∀ k : Nat, kleeneNat init post m ⊆ kleeneNat init post (m + k) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        exact Set.Subset.trans ih (kleeneNat_chain_step (post := post) hMono (m + k) init)
  rcases Nat.exists_eq_add_of_le hLe with ⟨k, hk⟩
  simpa [hk] using hAdd k

/--
Every successor Kleene iterate contains the initial states.
-/
theorem init_subset_kleeneNat_succ
    {State : Type u}
    {post : Post State} :
    ∀ (n : Nat) (init : Set State), init ⊆ kleeneNat init post (n + 1)
  | n, init => by
      intro s hs
      rw [kleeneNat_succ]
      exact Or.inl hs

/--
Lift one-step soundness to natural-number iteration soundness.

Assumptions:
- `hSound : Sound next gamma nextSharp`
- `hMono : MonotonePost next`

Conclusion:
- `iterateNat next (gamma a) n ⊆ gamma (iterateNatSharp nextSharp a n)`.
-/
theorem sound_iterateNat_of_sound
    {State : Type u}
    {Abstract : Type _}
    {next : Post State}
    {gamma : Gamma Abstract State}
    {nextSharp : PostSharp Abstract}
    (hSound : Sound next gamma nextSharp)
    (hMono : MonotonePost next) :
    ∀ (n : Nat) (a : Abstract),
      iterateNat next (gamma a) n ⊆
        gamma (iterateNatSharp nextSharp a n)
  | 0, a => by
      simp
  | n + 1, a => by
      simp only [iterateNat_succ, iterateNatSharp_succ]
      calc
        next (iterateNat next (gamma a) n)
            ⊆ next (gamma (iterateNatSharp nextSharp a n)) := by
              exact hMono (sound_iterateNat_of_sound (hSound := hSound) (hMono := hMono) n a)
        _ ⊆ gamma (nextSharp (iterateNatSharp nextSharp a n)) := by
              exact hSound (iterateNatSharp nextSharp a n)

end Iteration
end Framework
end AbsInterpLTS
