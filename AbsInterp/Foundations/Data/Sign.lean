/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import AbsInterp.Foundations.Data.BoolAbs
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Lattice

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
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .zero, .zero => .tt
  | .neg, .neg => .top
  | .pos, .pos => .top
  | _, _ => .ff

/-- Abstract less-or-equal test on signs. -/
def signLe : Sign -> Sign -> BoolAbs
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .neg, .neg => .top
  | .pos, .pos => .top
  | .neg, _ => .tt
  | .zero, .zero => .tt
  | .zero, .pos => .tt
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

end Data

end AbsInterp
