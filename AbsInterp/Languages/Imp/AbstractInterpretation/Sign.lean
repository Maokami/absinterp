/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import AbsInterp.Languages.Imp.Basic
public import AbsInterp.Foundations.Data.Sign
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

end Abstract

end Imp

end AbsInterp
