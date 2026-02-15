import Cslib.Init

import AbsInterpLTS.Framework.Semantics
import AbsInterpLTS.Framework.Soundness.Defs

namespace AbsInterpLTS
namespace Framework
namespace Iteration

open AbsInterpLTS.Framework

universe u v

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

/--
Inflationary concrete transformer predicate:
`states ⊆ post states`.
-/
def InflationaryPost
    {State : Type u}
    (post : Post State) : Prop :=
  ∀ states : Set State, states ⊆ post states

/-- Natural-number iterate scaffold for concrete post operators. -/
def iterateNat
    {State : Type u}
    (post : Post State)
    (init : Set State) :
    Nat -> Set State
  | 0 => init
  | n + 1 => post (iterateNat post init n)

/-- Natural-number iterate scaffold for abstract transformers. -/
def iterateNatSharp
    {Abstract : Type u}
    (postSharp : PostSharp Abstract)
    (init : Abstract) :
    Nat -> Abstract
  | 0 => init
  | n + 1 => postSharp (iterateNatSharp postSharp init n)

@[simp] theorem iterateNat_zero
    {State : Type u}
    (post : Post State)
    (init : Set State) :
    iterateNat post init 0 = init :=
  rfl

@[simp] theorem iterateNat_succ
    {State : Type u}
    (post : Post State)
    (init : Set State)
    (n : Nat) :
    iterateNat post init (n + 1) = post (iterateNat post init n) :=
  rfl

@[simp] theorem iterateNatSharp_zero
    {Abstract : Type u}
    (postSharp : PostSharp Abstract)
    (init : Abstract) :
    iterateNatSharp postSharp init 0 = init :=
  rfl

@[simp] theorem iterateNatSharp_succ
    {Abstract : Type u}
    (postSharp : PostSharp Abstract)
    (init : Abstract)
    (n : Nat) :
    iterateNatSharp postSharp init (n + 1) =
      postSharp (iterateNatSharp postSharp init n) :=
  rfl

/--
Monotonicity of natural-number iteration in the initial set.

Assumptions:
- `hMono : MonotonePost post`
- `hInit : init1 ⊆ init2`

Conclusion:
- `iterateNat post init1 n ⊆ iterateNat post init2 n`.
-/
theorem iterateNat_monotone_init
    {State : Type u}
    {post : Post State}
    (hMono : MonotonePost post) :
    ∀ n : Nat, ∀ {init1 init2 : Set State},
      init1 ⊆ init2 ->
      iterateNat post init1 n ⊆ iterateNat post init2 n
  | 0, init1, init2, hInit => hInit
  | n + 1, init1, init2, hInit => by
      simpa using
        hMono (iterateNat_monotone_init (hMono := hMono) n hInit)

/--
Successor-chain step for natural-number iteration.

Assumptions:
- `hMono : MonotonePost post`
- `hInfl : InflationaryPost post`

Conclusion:
- `iterateNat post init n ⊆ iterateNat post init (n + 1)`.
-/
theorem iterateNat_chain_step
    {State : Type u}
    {post : Post State}
    (hMono : MonotonePost post)
    (hInfl : InflationaryPost post) :
    ∀ (n : Nat) (init : Set State),
      iterateNat post init n ⊆ iterateNat post init (n + 1)
  | 0, init => by
      simpa using hInfl init
  | n + 1, init => by
      simpa using
        hMono (iterateNat_chain_step (hMono := hMono) (hInfl := hInfl) n init)

/--
Iteration chain monotonicity along natural-number indices.

Assumptions:
- `hMono : MonotonePost post`
- `hInfl : InflationaryPost post`
- `hLe : m ≤ n`

Conclusion:
- `iterateNat post init m ⊆ iterateNat post init n`.
-/
theorem iterateNat_chain_of_le
    {State : Type u}
    {post : Post State}
    (hMono : MonotonePost post)
    (hInfl : InflationaryPost post)
    {m n : Nat}
    (hLe : m ≤ n)
    (init : Set State) :
    iterateNat post init m ⊆ iterateNat post init n := by
  have hAdd :
      ∀ k : Nat, iterateNat post init m ⊆ iterateNat post init (m + k) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hStep :
            iterateNat post init (m + k) ⊆
              iterateNat post init (m + k + 1) :=
          iterateNat_chain_step
            (post := post)
            hMono
            hInfl
            (m + k)
            init
        exact Set.Subset.trans ih (by simpa [Nat.add_assoc] using hStep)
  rcases Nat.exists_eq_add_of_le hLe with ⟨k, hk⟩
  simpa [hk] using hAdd k

/--
Lift one-step soundness to natural-number iteration soundness.

Assumptions:
- `hSound : Sound post gamma postSharp`
- `hMono : MonotonePost post`

Conclusion:
- `iterateNat post (gamma a) n ⊆ gamma (iterateNatSharp postSharp a n)`.
-/
theorem sound_iterateNat_of_sound
    {State : Type u}
    {Abstract : Type v}
    {post : Post State}
    {gamma : Gamma Abstract State}
    {postSharp : PostSharp Abstract}
    (hSound : Sound post gamma postSharp)
    (hMono : MonotonePost post) :
    ∀ (n : Nat) (a : Abstract),
      iterateNat post (gamma a) n ⊆
        gamma (iterateNatSharp postSharp a n)
  | 0, a => by
      simp
  | n + 1, a => by
      have hIH :
          iterateNat post (gamma a) n ⊆
            gamma (iterateNatSharp postSharp a n) :=
        sound_iterateNat_of_sound
          (hSound := hSound)
          (hMono := hMono)
          n
          a
      have hToGamma :
          post (iterateNat post (gamma a) n) ⊆
            post (gamma (iterateNatSharp postSharp a n)) :=
        hMono hIH
      exact Set.Subset.trans hToGamma (hSound (iterateNatSharp postSharp a n))

end Iteration
end Framework
end AbsInterpLTS
