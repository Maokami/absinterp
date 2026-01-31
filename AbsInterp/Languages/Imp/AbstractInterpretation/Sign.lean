/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import AbsInterp.Languages.Imp.Basic
public import AbsInterp.Foundations.Data.Sign
public import AbsInterp.Foundations.Data.BoolAbs
public import AbsInterp.Foundations.Semantics.AbstractInterpretation.Basic

@[expose] public section

/-!
# Sign abstract domain for IMP

This file defines the sign abstract domain instance for IMP states.
-/

namespace AbsInterp

namespace Imp

namespace Abstract

universe u

variable {Var : Type u} [DecidableEq Var]

/-- Abstract domain of sign states: variables mapped to sign. -/
abbrev SignState (Var : Type u) := Var -> Data.Sign

/-- Concretization of sign states to sets of concrete states. -/
def gammaSignState (τ : SignState Var) : Set (State Var) :=
  {σ | ∀ x, σ x ∈ Data.gammaSign (τ x)}

/-- The sign abstract domain structure for IMP states. -/
def SignDomain : AbstractInterpretation.Domain (State Var) where
  A := SignState Var
  gamma := gammaSignState

/-- Abstract evaluation of arithmetic expressions in the sign domain. -/
def aevalSign : AExp Var -> SignState Var -> Data.Sign
  | .lit n, _ => Data.signOfInt n
  | .var x, τ => τ x
  | .add a b, τ => Data.signAdd (aevalSign a τ) (aevalSign b τ)
  | .sub a b, τ => Data.signSub (aevalSign a τ) (aevalSign b τ)
  | .mul a b, τ => Data.signMul (aevalSign a τ) (aevalSign b τ)

/-- Abstract evaluation of boolean expressions in the sign domain. -/
def bevalSign : BExp Var -> SignState Var -> Data.BoolAbs
  | .tt, _ => .tt
  | .ff, _ => .ff
  | .eq a b, τ => Data.signEq (aevalSign a τ) (aevalSign b τ)
  | .le a b, τ => Data.signLe (aevalSign a τ) (aevalSign b τ)
  | .not b, τ => Data.boolNot (bevalSign b τ)
  | .and a b, τ => Data.boolAnd (bevalSign a τ) (bevalSign b τ)

omit [DecidableEq Var] in
/-- Abstract evaluation of `AExp` is sound with respect to concretization. -/
theorem aevalSign_sound (a : AExp Var) (σ : State Var) (τ : SignState Var)
    (hσ : σ ∈ gammaSignState τ) :
    AExp.eval a σ ∈ Data.gammaSign (aevalSign a τ) := by
  induction a with
  | lit n =>
      simpa [AExp.eval, aevalSign] using Data.signOfInt_sound n
  | var x =>
      simpa [AExp.eval, aevalSign, gammaSignState] using hσ x
  | add _ _ ha hb =>
      simpa [AExp.eval, aevalSign] using Data.signAdd_sound ha hb
  | sub _ _ ha hb =>
      simpa [AExp.eval, aevalSign] using Data.signSub_sound ha hb
  | mul _ _ ha hb =>
      simpa [AExp.eval, aevalSign] using Data.signMul_sound ha hb

omit [DecidableEq Var] in
/-- Abstract evaluation of `BExp` is sound with respect to concretization. -/
theorem bevalSign_sound (b : BExp Var) (σ : State Var) (τ : SignState Var)
    (hσ : σ ∈ gammaSignState τ) :
    BExp.eval b σ ∈ Data.gammaBoolAbs (bevalSign b τ) := by
  induction b with
  | tt | ff =>
      simp [BExp.eval, bevalSign, Data.gammaBoolAbs]
  | eq a b =>
      have ha' := aevalSign_sound a σ τ hσ
      have hb' := aevalSign_sound b σ τ hσ
      simpa [BExp.eval, bevalSign] using Data.signEq_sound ha' hb'
  | le a b =>
      have ha' := aevalSign_sound a σ τ hσ
      have hb' := aevalSign_sound b σ τ hσ
      simpa [BExp.eval, bevalSign] using Data.signLe_sound ha' hb'
  | not b hb =>
      simpa [BExp.eval, bevalSign] using Data.boolNot_sound hb
  | and b1 b2 hb1 hb2 =>
      simpa [BExp.eval, bevalSign] using Data.boolAnd_sound hb1 hb2

end Abstract

end Imp

end AbsInterp
