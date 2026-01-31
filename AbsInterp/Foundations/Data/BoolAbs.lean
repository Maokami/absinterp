/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Lattice

@[expose] public section

/-!
# Boolean abstract domain

A four-valued abstract boolean domain: bottom, false, true, and top.
This is the finite lattice corresponding to subsets of Bool.
-/

namespace AbsInterp

namespace Data

/-- Abstract booleans (bottom/false/true/top). -/
inductive BoolAbs
  | bot
  | ff
  | tt
  | top
  deriving DecidableEq

/-- Concretization of abstract booleans to sets of Bool. -/
def gammaBoolAbs : BoolAbs -> Set Bool
  | .bot => {}
  | .ff => {false}
  | .tt => {true}
  | .top => Set.univ

/-- Information order on abstract booleans. -/
inductive BoolAbs.LE : BoolAbs -> BoolAbs -> Prop
  | bot (a) : LE .bot a
  | top (a) : LE a .top
  | ff : LE .ff .ff
  | tt : LE .tt .tt

instance : LE BoolAbs := ⟨BoolAbs.LE⟩

instance : Bot BoolAbs := ⟨BoolAbs.bot⟩

instance : Top BoolAbs := ⟨BoolAbs.top⟩

/-- Join on abstract booleans. -/
def BoolAbs.sup : BoolAbs -> BoolAbs -> BoolAbs
  | .bot, b => b
  | a, .bot => a
  | .ff, .ff => .ff
  | .tt, .tt => .tt
  | _, _ => .top

instance : DecidableLE BoolAbs := by
  intro a b
  cases a <;> cases b <;> first
    | exact isTrue (by constructor)
    | exact isFalse (by intro h; cases h)

instance : PartialOrder BoolAbs where
  le := (· ≤ ·)
  le_refl a := by cases a <;> constructor
  le_trans a b c hab hbc := by
    cases hab <;> cases hbc <;> constructor
  le_antisymm a b hab hba := by
    cases hab <;> cases hba <;> rfl

instance : SemilatticeSup BoolAbs where
  sup := BoolAbs.sup
  le_sup_left a b := by cases a <;> cases b <;> constructor
  le_sup_right a b := by cases a <;> cases b <;> constructor
  sup_le a b c hac hbc := by
    cases a <;> cases b <;> cases c <;> cases hac <;> cases hbc <;> constructor

/-- Concretization is monotone with respect to the abstract boolean order. -/
theorem gammaBoolAbs_mono {a b : BoolAbs} (h : a ≤ b) : gammaBoolAbs a ⊆ gammaBoolAbs b := by
  intro v hv
  cases h with
  | bot b => cases hv
  | top a => simp [gammaBoolAbs]
  | ff | tt => simpa

/-- Abstract boolean negation. -/
def boolNot : BoolAbs -> BoolAbs
  | .bot => .bot
  | .ff => .tt
  | .tt => .ff
  | .top => .top

/-- Abstract boolean conjunction. -/
def boolAnd : BoolAbs -> BoolAbs -> BoolAbs
  | .bot, _ | _, .bot => .bot
  | .ff, _ | _, .ff => .ff
  | .tt, .tt => .tt
  | _, _ => .top

end Data

end AbsInterp
