import Cslib.Init
import Mathlib.Data.Set.Lattice
import AbsInterp.Framework.Domains

namespace AbsInterp
namespace Domains

open AbsInterp.Framework.Domains

/-!
# Parity Domain

A simple 4-element abstract domain tracking integer parity (even/odd).
Used as a validation target for the generic IMP analysis framework.
-/

/-- Four-point parity domain: `⊥`, `even`, `odd`, `⊤`. -/
inductive Parity where
  | bot
  | even
  | odd
  | top
  deriving DecidableEq, Repr

instance : Bot Parity where
  bot := .bot

/-- Concretization map from abstract parity to sets of integers. -/
def gammaParity : Parity → Set Int
  | .bot => ∅
  | .even => { n : Int | n % 2 = 0 }
  | .odd => { n : Int | n % 2 ≠ 0 }
  | .top => Set.univ

/-- Order on the parity lattice. -/
def leParity : Parity → Parity → Prop
  | .bot, _ => True
  | _, .top => True
  | .even, .even => True
  | .odd, .odd => True
  | _, _ => False

instance : DecidableRel leParity := by
  intro a b; cases a <;> cases b <;> simp [leParity] <;> exact inferInstance

theorem leParity_refl : ∀ a : Parity, leParity a a := by
  intro a; cases a <;> simp [leParity]

theorem leParity_trans : ∀ {a b c : Parity}, leParity a b → leParity b c → leParity a c := by
  intro a b c hab hbc; cases a <;> cases b <;> cases c <;> simp_all [leParity]

theorem gammaParity_monotone : ∀ {a b : Parity}, leParity a b → gammaParity a ⊆ gammaParity b := by
  intro a b hab; cases a <;> cases b <;> simp_all [leParity, gammaParity, Set.subset_univ]

/-- Join on the parity lattice. -/
def joinParity : Parity → Parity → Parity
  | .bot, a => a
  | a, .bot => a
  | .even, .even => .even
  | .odd, .odd => .odd
  | _, _ => .top

theorem joinParity_sound : ∀ a b : Parity, gammaParity a ∪ gammaParity b ⊆ gammaParity (joinParity a b) := by
  intro a b n hn
  cases a <;> cases b <;> simp_all [joinParity, gammaParity, Set.mem_union, Set.mem_empty_iff_false]

/-- The complete gamma-only domain instance for Parity. -/
def parityGammaOnlyDomain : GammaOnlyDomain Parity Int where
  gamma := gammaParity
  le := leParity
  le_refl := leParity_refl
  le_trans := leParity_trans
  gamma_monotone := gammaParity_monotone
  top := .top
  gamma_top := fun _ => Set.mem_univ _
  join := joinParity
  join_sound := joinParity_sound

/-- Abstract a concrete integer constant by its parity. -/
def constParity (n : Int) : Parity :=
  if n % 2 = 0 then .even else .odd

theorem constParity_sound (n : Int) : n ∈ gammaParity (constParity n) := by
  unfold constParity
  by_cases h : n % 2 = 0 <;> simp_all [gammaParity]

/-- Abstract addition transfer for the parity domain. -/
def addParityTransfer : Parity → Parity → Parity
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .even, .even => .even
  | .even, .odd => .odd
  | .odd, .even => .odd
  | .odd, .odd => .even

theorem addParityTransfer_sound
    {a b : Parity} {m n : Int}
    (hm : m ∈ gammaParity a)
    (hn : n ∈ gammaParity b) :
    m + n ∈ gammaParity (addParityTransfer a b) := by
  cases a <;> cases b <;> simp_all [addParityTransfer, gammaParity]
  all_goals omega

/-- Refine a parity value under a nonzero assumption (identity — parity cannot refine). -/
def assumeNonzeroParity : Parity → Parity := id

theorem assumeNonzeroParity_sound
    {a : Parity} {n : Int}
    (hn : n ∈ gammaParity a)
    (_ : n ≠ 0) :
    n ∈ gammaParity (assumeNonzeroParity a) := hn

/-- Refine a parity value under a zero assumption. -/
def assumeZeroParity : Parity → Parity
  | .bot => .bot
  | .even => .even
  | .odd => .bot
  | .top => .even

theorem assumeZeroParity_sound
    {a : Parity} {n : Int}
    (hn : n ∈ gammaParity a)
    (hZero : n = 0) :
    n ∈ gammaParity (assumeZeroParity a) := by
  subst hZero
  cases a <;> simp_all [assumeZeroParity, gammaParity]

end Domains
end AbsInterp
