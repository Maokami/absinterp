/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import AbsInterp.Foundations.Data.BoolAbs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Lattice
import Mathlib.Tactic

@[expose] public section

/-!
# Sign lattice

A flat lattice of integer signs with top and bottom, plus a concretization
function to sets of integers.
-/

namespace AbsInterp

namespace Data

/-- Sign abstraction for integers (flat lattice with top and bottom). -/
inductive Sign
  | bot
  | neg
  | zero
  | pos
  | top
  deriving DecidableEq

/-- Concretization of sign values to sets of integers. -/
def gammaSign : Sign -> Set Int
  | .bot => {}
  | .neg => {n | n < 0}
  | .zero => {0}
  | .pos => {n | 0 < n}
  | .top => Set.univ

/-- Information order on signs. -/
inductive Sign.LE : Sign -> Sign -> Prop
  | bot (a) : LE .bot a
  | top (a) : LE a .top
  | neg : LE .neg .neg
  | zero : LE .zero .zero
  | pos : LE .pos .pos

instance : LE Sign := ⟨Sign.LE⟩

instance : Bot Sign := ⟨Sign.bot⟩

instance : Top Sign := ⟨Sign.top⟩

/-- Join on signs. -/
def Sign.sup : Sign -> Sign -> Sign
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .neg, .neg => .neg
  | .zero, .zero => .zero
  | .pos, .pos => .pos
  | _, _ => .top

/-- Sign of a concrete integer. -/
def signOfInt (n : Int) : Sign :=
  if n < 0 then
    .neg
  else if n = 0 then
    .zero
  else
    .pos

/-- Sign negation. -/
def signNeg : Sign -> Sign
  | .bot => .bot
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg
  | .top => .top

/-- Sign addition (sound but not necessarily precise). -/
def signAdd : Sign -> Sign -> Sign
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .zero, b => b
  | a, .zero => a
  | .neg, .neg => .neg
  | .pos, .pos => .pos
  | _, _ => .top

/-- Sign multiplication (sound but not necessarily precise). -/
def signMul : Sign -> Sign -> Sign
  | .bot, _ => .bot
  | _, .bot => .bot
  | .zero, _ => .zero
  | _, .zero => .zero
  | .top, _ => .top
  | _, .top => .top
  | .neg, .neg => .pos
  | .pos, .pos => .pos
  | .neg, .pos => .neg
  | .pos, .neg => .neg

/-- Sign subtraction. -/
def signSub (a b : Sign) : Sign :=
  signAdd a (signNeg b)

/-- Abstract equality test on signs. -/
def signEq : Sign -> Sign -> BoolAbs
  | .bot, _ | _, .bot => .bot
  | .top, _ | _, .top => .top
  | .zero, .zero => .tt
  | .neg, .neg | .pos, .pos => .top
  | _, _ => .ff

/-- Abstract less-or-equal test on signs. -/
def signLe : Sign -> Sign -> BoolAbs
  | .bot, _ | _, .bot => .bot
  | .top, _ | _, .top => .top
  | .neg, .neg | .pos, .pos => .top
  | .neg, _ => .tt
  | .zero, .zero | .zero, .pos => .tt
  | _, _ => .ff

instance : DecidableLE Sign := by
  intro a b
  cases a <;> cases b <;> first
    | exact isTrue (by constructor)
    | exact isFalse (by intro h; cases h)

instance : PartialOrder Sign where
  le := (· ≤ ·)
  le_refl a := by cases a <;> constructor
  le_trans a b c hab hbc := by
    cases hab <;> cases hbc <;> constructor
  le_antisymm a b hab hba := by
    cases hab <;> cases hba <;> rfl

instance : SemilatticeSup Sign where
  sup := Sign.sup
  le_sup_left a b := by cases a <;> cases b <;> constructor
  le_sup_right a b := by cases a <;> cases b <;> constructor
  sup_le a b c hac hbc := by
    cases a <;> cases b <;> cases c <;> cases hac <;> cases hbc <;> constructor

/-- Concretization is monotone with respect to the sign order. -/
theorem gammaSign_mono {a b : Sign} (h : a ≤ b) : gammaSign a ⊆ gammaSign b := by
  intro n hn
  cases h with
  | bot b => cases hn
  | top a => simp [gammaSign]
  | neg | zero | pos => simpa

/-- `signOfInt` is sound with respect to concretization. -/
theorem signOfInt_sound (n : Int) : n ∈ gammaSign (signOfInt n) := by
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · simp [signOfInt, gammaSign, hneg]
  · simp [signOfInt, gammaSign, hzero]
  · have hneg' : ¬ n < 0 := not_lt_of_gt hpos
    have hzero' : n ≠ 0 := ne_of_gt hpos
    simp [signOfInt, gammaSign, hneg', hzero', hpos]

/-- `signNeg` is sound with respect to concretization. -/
theorem signNeg_sound {a : Sign} {x : Int} (hx : x ∈ gammaSign a) :
    -x ∈ gammaSign (signNeg a) := by
  cases a <;> simp_all [gammaSign, signNeg]

/-- `signAdd` is sound with respect to concretization. -/
theorem signAdd_sound {a b : Sign} {x y : Int}
    (hx : x ∈ gammaSign a) (hy : y ∈ gammaSign b) :
    x + y ∈ gammaSign (signAdd a b) := by
  cases a <;> cases b <;> simp [signAdd, gammaSign] at hx hy ⊢
  all_goals
    nlinarith

/-- `signMul` is sound with respect to concretization. -/
theorem signMul_sound {a b : Sign} {x y : Int}
    (hx : x ∈ gammaSign a) (hy : y ∈ gammaSign b) :
    x * y ∈ gammaSign (signMul a b) := by
  cases a <;> cases b <;> simp_all [signMul, gammaSign]
  all_goals
    nlinarith

/-- `signSub` is sound with respect to concretization. -/
theorem signSub_sound {a b : Sign} {x y : Int}
    (hx : x ∈ gammaSign a) (hy : y ∈ gammaSign b) :
    x - y ∈ gammaSign (signSub a b) := by
  have hy' : -y ∈ gammaSign (signNeg b) := signNeg_sound hy
  simpa [signSub, sub_eq_add_neg] using (signAdd_sound (a := a) (b := signNeg b) hx hy')

/-- `signEq` is sound with respect to concretization. -/
theorem signEq_sound {a b : Sign} {x y : Int}
    (hx : x ∈ gammaSign a) (hy : y ∈ gammaSign b) :
    decide (x = y) ∈ gammaBoolAbs (signEq a b) := by
  cases a <;> cases b <;>
    simp [signEq, gammaSign, gammaBoolAbs] at hx hy ⊢
  all_goals
    try nlinarith
  all_goals
    by_cases h : x = y <;> simp [h]

/-- `signLe` is sound with respect to concretization. -/
theorem signLe_sound {a b : Sign} {x y : Int}
    (hx : x ∈ gammaSign a) (hy : y ∈ gammaSign b) :
    decide (x ≤ y) ∈ gammaBoolAbs (signLe a b) := by
  cases a <;> cases b <;>
    simp [signLe, gammaSign, gammaBoolAbs] at hx hy ⊢
  all_goals
    try nlinarith
  all_goals
    exact lt_or_ge y x

end Data

end AbsInterp
