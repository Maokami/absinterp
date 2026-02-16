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
Inflationary concrete transformer predicate:
`states ⊆ next states`.
-/
def InflationaryPost
    {State : Type u}
    (next : Post State) : Prop :=
  ∀ states : Set State, states ⊆ next states

/--
Collecting-style fixpoint operator for reachability:
`reachF init stepPost states = init ∪ stepPost states`.
-/
def reachF
    {State : Type u}
    (init : Set State)
    (stepPost : Post State) :
    Post State :=
  fun states => init ∪ stepPost states

/-- Natural-number iterate scaffold for concrete next-step operators. -/
def iterateNat
    {State : Type u}
    (next : Post State)
    (init : Set State) :
    Nat -> Set State
  | 0 => init
  | n + 1 => next (iterateNat next init n)

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
Successor-chain step for natural-number iteration.

Assumptions:
- `hMono : MonotonePost next`
- `hInfl : InflationaryPost next`

Conclusion:
- `iterateNat next init n ⊆ iterateNat next init (n + 1)`.
-/
theorem iterateNat_chain_step
    {State : Type u}
    {next : Post State}
    (hMono : MonotonePost next)
    (hInfl : InflationaryPost next) :
    ∀ (n : Nat) (init : Set State),
      iterateNat next init n ⊆ iterateNat next init (n + 1)
  | 0, init => by
      simpa using hInfl init
  | n + 1, init => by
      simpa using
        hMono (iterateNat_chain_step (hMono := hMono) (hInfl := hInfl) n init)

/--
Iteration chain monotonicity along natural-number indices.

Assumptions:
- `hMono : MonotonePost next`
- `hInfl : InflationaryPost next`
- `hLe : m ≤ n`

Conclusion:
- `iterateNat next init m ⊆ iterateNat next init n`.
-/
theorem iterateNat_chain_of_le
    {State : Type u}
    {next : Post State}
    (hMono : MonotonePost next)
    (hInfl : InflationaryPost next)
    {m n : Nat}
    (hLe : m ≤ n)
    (init : Set State) :
    iterateNat next init m ⊆ iterateNat next init n := by
  have hAdd :
      ∀ k : Nat, iterateNat next init m ⊆ iterateNat next init (m + k) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        exact Set.Subset.trans ih (iterateNat_chain_step (next := next) hMono hInfl (m + k) init)
  rcases Nat.exists_eq_add_of_le hLe with ⟨k, hk⟩
  simpa [hk] using hAdd k

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
