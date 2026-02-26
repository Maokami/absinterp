import Cslib.Init

import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Framework.Semantics
import AbsInterpLTS.Framework.Soundness.Defs

namespace AbsInterpLTS
namespace Framework
namespace Iteration

open AbsInterpLTS.Framework

universe u

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

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
