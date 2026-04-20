import Cslib.Init
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

theorem leParity_antisymm : ∀ {a b : Parity}, leParity a b → leParity b a → a = b := by
  intro a b hab hba; cases a <;> cases b <;> simp_all [leParity]

instance : PartialOrder Parity where
  le := leParity
  le_refl := leParity_refl
  le_trans := @leParity_trans
  le_antisymm _ _ := leParity_antisymm

instance : OrderTop Parity where
  top := .top
  le_top a := by cases a <;> simp [leParity, LE.le]

theorem gammaParity_monotone : ∀ ⦃a b : Parity⦄, leParity a b → gammaParity a ⊆ gammaParity b := by
  intro a b hab; cases a <;> cases b <;> simp_all [leParity, gammaParity, Set.subset_univ]

/-- Join on the parity lattice. -/
def joinParity : Parity → Parity → Parity
  | .bot, a => a
  | a, .bot => a
  | .even, .even => .even
  | .odd, .odd => .odd
  | _, _ => .top

theorem joinParity_le_left (a b : Parity) : a ≤ joinParity a b := by
  cases a <;> cases b <;> simp [LE.le, leParity, joinParity]

theorem joinParity_le_right (a b : Parity) : b ≤ joinParity a b := by
  cases a <;> cases b <;> simp [LE.le, leParity, joinParity]

theorem joinParity_le_of_le {a b c : Parity} (ha : a ≤ c) (hb : b ≤ c) :
    joinParity a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [LE.le, leParity, joinParity]

instance : SemilatticeSup Parity where
  sup := joinParity
  le_sup_left := joinParity_le_left
  le_sup_right := joinParity_le_right
  sup_le _ _ _ ha hb := joinParity_le_of_le ha hb

/-- The complete concretization-domain instance for Parity. -/
def parityConcretizationDomain : ConcretizationDomain Parity Int where
  gamma := gammaParity
  gamma_monotone := gammaParity_monotone
  gamma_top := fun _ => Set.mem_univ _

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

/-- Intersection on the parity lattice. -/
def intersectParity : Parity → Parity → Parity
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, a => a
  | a, .top => a
  | .even, .even => .even
  | .odd, .odd => .odd
  | _, _ => .bot

theorem intersectParity_sound
    {a b : Parity} {n : Int}
    (ha : n ∈ gammaParity a)
    (hb : n ∈ gammaParity b) :
    n ∈ gammaParity (intersectParity a b) := by
  cases a <;> cases b <;> simp [intersectParity, gammaParity] at ha hb ⊢ <;> omega

theorem intersectParity_reductive (a b : Parity) :
    intersectParity a b ≤ a ∧ intersectParity a b ≤ b := by
  cases a <;> cases b <;> simp [LE.le, leParity, intersectParity]

/-- Filter a parity value under a nonzero assumption (identity — parity cannot refine). -/
def filterNonzeroParity : Parity → Parity := id

theorem filterNonzeroParity_sound
    {a : Parity} {n : Int}
    (hn : n ∈ gammaParity a)
    (_ : n ≠ 0) :
    n ∈ gammaParity (filterNonzeroParity a) := hn

theorem filterNonzeroParity_reductive :
    AbsInterp.Framework.Domains.ReductiveFilter filterNonzeroParity :=
  AbsInterp.Framework.Domains.ReductiveFilter.id

/-- Filter a parity value under a zero assumption. -/
def filterZeroParity : Parity → Parity
  | .bot => .bot
  | .even => .even
  | .odd => .bot
  | .top => .even

theorem filterZeroParity_sound
    {a : Parity} {n : Int}
    (hn : n ∈ gammaParity a)
    (hZero : n = 0) :
    n ∈ gammaParity (filterZeroParity a) := by
  subst hZero
  cases a <;> simp_all [filterZeroParity, gammaParity]

theorem filterZeroParity_reductive :
    AbsInterp.Framework.Domains.ReductiveFilter filterZeroParity := by
  intro a
  cases a <;> simp [LE.le, leParity, filterZeroParity]

end Domains
end AbsInterp
