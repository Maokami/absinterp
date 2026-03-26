import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Framework.Domains
import Examples.IMP.Semantics

namespace Examples.IMP

open AbsInterpLTS.Framework.Domains

universe u

/-!
# IMP Analysis Domain Interface

`IMPAnalysisDomain` captures the domain-specific obligations for an IMP
abstract analysis, so that transfer functions and soundness proofs can be
written once generically.

The interface sits between the scalar abstract domain (`GammaOnlyDomain A Int`)
and the IMP-specific analysis machinery. A concrete instance must supply:

- scalar expression evaluation primitives (`const`, `addTransfer`) with
  soundness,
- branch refinement operators (`assumeNonzero`, `assumeZero`) with soundness,
- a proof that the bottom element has empty concretization.
-/

/--
Domain-specific obligations for a generic IMP abstract analysis.

An instance packages a scalar `GammaOnlyDomain` together with the transfer
primitives and soundness contracts needed by the generic IMP transfer function
and its soundness proof.
-/
structure IMPAnalysisDomain (A : Type u) [Bot A] where
  /-- The underlying scalar gamma-only domain over integers. -/
  scalarDomain : GammaOnlyDomain A Int
  /-- The bottom element has empty concretization. -/
  gamma_bot : scalarDomain.gamma ⊥ = ∅
  /-- Abstract a concrete integer constant. -/
  const : Int → A
  /-- Constant abstraction is sound. -/
  const_sound : ∀ n : Int, n ∈ scalarDomain.gamma (const n)
  /-- Abstract addition transfer. -/
  addTransfer : A → A → A
  /-- Addition transfer is sound. -/
  addTransfer_sound : ∀ {a₁ a₂ : A} {v₁ v₂ : Int},
    v₁ ∈ scalarDomain.gamma a₁ → v₂ ∈ scalarDomain.gamma a₂ →
    v₁ + v₂ ∈ scalarDomain.gamma (addTransfer a₁ a₂)
  /-- Refine an abstract value under a nonzero assumption. -/
  assumeNonzero : A → A
  /-- Nonzero refinement is sound. -/
  assumeNonzero_sound : ∀ {a : A} {v : Int},
    v ∈ scalarDomain.gamma a → v ≠ 0 → v ∈ scalarDomain.gamma (assumeNonzero a)
  /-- Refine an abstract value under a zero assumption. -/
  assumeZero : A → A
  /-- Zero refinement is sound. -/
  assumeZero_sound : ∀ {a : A} {v : Int},
    v ∈ scalarDomain.gamma a → v = 0 → v ∈ scalarDomain.gamma (assumeZero a)

namespace IMPAnalysisDomain

variable {A : Type u} [Bot A] (d : IMPAnalysisDomain A)

/-- Convenience accessor for the scalar concretization function. -/
abbrev gamma : A → Set Int := d.scalarDomain.gamma

/-- Convenience accessor for the scalar join. -/
abbrev join : A → A → A := d.scalarDomain.join

/-- Convenience accessor for the scalar top element. -/
abbrev top : A := d.scalarDomain.top

end IMPAnalysisDomain

end Examples.IMP
