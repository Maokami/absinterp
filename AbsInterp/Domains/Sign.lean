import Cslib.Init
import Mathlib.Data.Set.Lattice
import AbsInterp.Framework.Domains

namespace AbsInterp
namespace Domains

/--
Seven-point sign domain:
`⊥`, singletons (`neg`, `zero`, `pos`), pair-wise joins (`nonpos`, `nonneg`), and `⊤`.
-/
inductive Sign where
  | bot
  | neg
  | zero
  | pos
  | nonpos
  | nonneg
  | top
  deriving DecidableEq, Repr

instance : Bot Sign where
  bot := .bot

/-- Concretization map from abstract signs to sets of integers. -/
def gammaSign : Sign -> Set Int
  | .bot => ∅
  | .neg => { n : Int | n < 0 }
  | .zero => { n : Int | n = 0 }
  | .pos => { n : Int | 0 < n }
  | .nonpos => { n : Int | n < 0 ∨ n = 0 }
  | .nonneg => { n : Int | n = 0 ∨ 0 < n }
  | .top => (Set.univ : Set Int)

/-- Domain order induced by concretization inclusion. -/
def leSign (a b : Sign) : Prop :=
  gammaSign a ⊆ gammaSign b

theorem leSign_refl (a : Sign) : leSign a a :=
  fun _ hn => hn

theorem leSign_trans {a b c : Sign} (hAB : leSign a b) (hBC : leSign b c) : leSign a c :=
  fun _ hn => hBC (hAB hn)

instance : Preorder Sign where
  le := leSign
  le_refl := leSign_refl
  le_trans := @leSign_trans

theorem gammaSign_monotone_of_leSign {a b : Sign} (hAB : a ≤ b) :
    gammaSign a ⊆ gammaSign b :=
  hAB

/-- `top` concretizes to all integers. -/
theorem gammaSign_top (n : Int) : n ∈ gammaSign Sign.top := by
  change True
  trivial

private def hasNeg : Sign -> Bool
  | .bot => false
  | .neg => true
  | .zero => false
  | .pos => false
  | .nonpos => true
  | .nonneg => false
  | .top => true

private def hasZero : Sign -> Bool
  | .bot => false
  | .neg => false
  | .zero => true
  | .pos => false
  | .nonpos => true
  | .nonneg => true
  | .top => true

private def hasPos : Sign -> Bool
  | .bot => false
  | .neg => false
  | .zero => false
  | .pos => true
  | .nonpos => false
  | .nonneg => true
  | .top => true

private def signOfFlags (neg zero pos : Bool) : Sign :=
  match neg, zero, pos with
  | false, false, false => .bot
  | true, false, false => .neg
  | false, true, false => .zero
  | false, false, true => .pos
  | true, true, false => .nonpos
  | false, true, true => .nonneg
  | true, false, true => .top
  | true, true, true => .top

/-- Join on signs, with `{neg,pos}` normalized to `top`. -/
def joinSign (a b : Sign) : Sign :=
  signOfFlags
    (hasNeg a || hasNeg b)
    (hasZero a || hasZero b)
    (hasPos a || hasPos b)

/-- `joinSign` soundly over-approximates union concretization. -/
theorem joinSign_sound (a b : Sign) :
    gammaSign a ∪ gammaSign b ⊆ gammaSign (joinSign a b) := by
  intro n hn
  cases a <;> cases b <;>
    simp [gammaSign, joinSign, signOfFlags, hasNeg, hasZero, hasPos] at hn ⊢ <;>
    tauto

@[simp] theorem joinSign_bot_left (a : Sign) :
    joinSign .bot a = a := by
  cases a <;> rfl

@[simp] theorem joinSign_bot_right (a : Sign) :
    joinSign a .bot = a := by
  cases a <;> rfl

/-- Exact sign for an integer literal. -/
def constSign (n : Int) : Sign :=
  if n < 0 then .neg else if n = 0 then .zero else .pos

/-- `constSign` contains the concrete integer it abstracts. -/
theorem constSign_sound (n : Int) :
    n ∈ gammaSign (constSign n) := by
  by_cases hNeg : n < 0
  · simp [constSign, gammaSign, hNeg]
  · by_cases hZero : n = 0
    · simp [constSign, gammaSign, hZero]
    · have hPos : 0 < n := by omega
      simp [constSign, gammaSign, hNeg, hZero, hPos]

/--
Sound abstract addition on signs.

This is intentionally lightweight: it aims for a useful, sound
over-approximation rather than maximal precision.
-/
def addTransfer : Sign -> Sign -> Sign
  | .bot, _ => .bot
  | _, .bot => .bot
  | .zero, b => b
  | a, .zero => a
  | .neg, .neg => .neg
  | .neg, .nonpos => .neg
  | .neg, .pos => .top
  | .neg, .nonneg => .top
  | .neg, .top => .top
  | .pos, .neg => .top
  | .pos, .pos => .pos
  | .pos, .nonpos => .top
  | .pos, .nonneg => .pos
  | .pos, .top => .top
  | .nonpos, .neg => .neg
  | .nonpos, .pos => .top
  | .nonpos, .nonpos => .nonpos
  | .nonpos, .nonneg => .top
  | .nonpos, .top => .top
  | .nonneg, .neg => .top
  | .nonneg, .pos => .pos
  | .nonneg, .nonpos => .top
  | .nonneg, .nonneg => .nonneg
  | .nonneg, .top => .top
  | .top, .neg => .top
  | .top, .pos => .top
  | .top, .nonpos => .top
  | .top, .nonneg => .top
  | .top, .top => .top

/-- `addTransfer` soundly abstracts integer addition. -/
theorem addTransfer_sound
    {a b : Sign}
    {m n : Int}
    (hm : m ∈ gammaSign a)
    (hn : n ∈ gammaSign b) :
    m + n ∈ gammaSign (addTransfer a b) := by
  cases a <;> cases b <;>
    simp [gammaSign, addTransfer] at hm hn ⊢ <;>
    omega

/-- Refine a sign by assuming the concrete value is nonzero. -/
def assumeNonzero : Sign -> Sign
  | .bot => .bot
  | .neg => .neg
  | .zero => .bot
  | .pos => .pos
  | .nonpos => .neg
  | .nonneg => .pos
  | .top => .top

/-- Refine a sign by assuming the concrete value is exactly zero. -/
def assumeZero : Sign -> Sign
  | .bot => .bot
  | .neg => .bot
  | .zero => .zero
  | .pos => .bot
  | .nonpos => .zero
  | .nonneg => .zero
  | .top => .zero

/-- `assumeNonzero` is sound for a concrete witness known to be nonzero. -/
theorem assumeNonzero_sound
    {a : Sign}
    {n : Int}
    (hn : n ∈ gammaSign a)
    (hNe : n ≠ 0) :
    n ∈ gammaSign (assumeNonzero a) := by
  cases a <;>
    simp [gammaSign, assumeNonzero] at hn ⊢ <;>
    omega

/-- `assumeZero` is sound for a concrete witness known to be zero. -/
theorem assumeZero_sound
    {a : Sign}
    {n : Int}
    (hn : n ∈ gammaSign a)
    (hZero : n = 0) :
    n ∈ gammaSign (assumeZero a) := by
  cases a <;>
    simp [gammaSign, assumeZero] at hn ⊢ <;>
    omega

/-- Baseline unary transfer shape: abstract negation. -/
def negTransfer : Sign -> Sign
  | .bot => .bot
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg
  | .nonpos => .nonneg
  | .nonneg => .nonpos
  | .top => .top

theorem negTransfer_sound {a : Sign} {n : Int} (hn : n ∈ gammaSign a) :
    -n ∈ gammaSign (negTransfer a) := by
  cases a with
  | bot =>
      change False at hn
      exact False.elim hn
  | neg =>
      change n < 0 at hn
      change 0 < -n
      omega
  | zero =>
      change n = 0 at hn
      change -n = 0
      omega
  | pos =>
      change 0 < n at hn
      change -n < 0
      omega
  | nonpos =>
      change n < 0 ∨ n = 0 at hn
      change -n = 0 ∨ 0 < -n
      omega
  | nonneg =>
      change n = 0 ∨ 0 < n at hn
      change -n < 0 ∨ -n = 0
      omega
  | top =>
      change True at hn
      change True
      trivial

/-- Gamma-only interface instance for the sign domain. -/
def signGammaOnlyDomain :
    AbsInterp.Framework.Domains.GammaOnlyDomain Sign Int where
  gamma := gammaSign
  le := leSign
  le_refl := leSign_refl
  le_trans := leSign_trans
  gamma_monotone := gammaSign_monotone_of_leSign
  top := Sign.top
  gamma_top := gammaSign_top
  join := joinSign
  join_sound := joinSign_sound

end Domains
end AbsInterp
