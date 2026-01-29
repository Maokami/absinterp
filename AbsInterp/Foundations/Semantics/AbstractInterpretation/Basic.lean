/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-!
# Abstract Interpretation (basic framework)

This file provides minimal scaffolding for abstract interpretation:
abstract domains with a concretization map, abstract transformers,
and the basic soundness predicate.
-/

namespace AbsInterp

namespace AbstractInterpretation

universe u v

/--
An abstract domain over states, equipped with a carrier and a concretization map.
Order/lattice structure is provided separately via typeclasses.
-/
structure Domain (State : Type u) where
  /-- Carrier of abstract elements. -/
  A : Type v
  /-- Concretization: map abstract elements to sets of states. -/
  gamma : A -> Set State

/-- A concrete transformer over sets of states. -/
abbrev ConcreteTransformer (State : Type u) := Set State -> Set State

/-- An abstract transformer over an abstract domain. -/
abbrev AbstractTransformer {State : Type u} (D : Domain State) := D.A -> D.A

/-- Soundness of an abstract transformer with respect to a concrete one. -/
def Sound {State : Type u} (D : Domain State)
    (Post : ConcreteTransformer State)
    (PostAbs : AbstractTransformer D) : Prop :=
  forall a, D.gamma (PostAbs a) ⊆ Post (D.gamma a)

end AbstractInterpretation

end AbsInterp
