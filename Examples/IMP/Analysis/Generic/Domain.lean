import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Domains
import Examples.IMP.Semantics

namespace Examples.IMP

open AbsInterp.Framework.Domains

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
structure IMPAnalysisDomain
    (A : Type u) [Bot A] [Preorder A] [OrderTop A] [Max A] where
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
  /-- Nonzero refinement is sound (`SoundAssume` with `P := (· ≠ 0)`). -/
  assumeNonzero_sound :
    SoundAssume scalarDomain.gamma (· ≠ 0) assumeNonzero
  /-- Refine an abstract value under a zero assumption. -/
  assumeZero : A → A
  /-- Zero refinement is sound (`SoundAssume` with `P := (· = 0)`). -/
  assumeZero_sound :
    SoundAssume scalarDomain.gamma (· = 0) assumeZero
  /-- Backward refinement for addition under nonzero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ ≠ 0`, refine both. -/
  assumeNonzeroAdd : A → A → A × A := fun a₁ a₂ => (a₁, a₂)
  /-- Nonzero-add backward refinement is sound (`SoundBackwardRefine` with
      `rel := fun v₁ v₂ => v₁ + v₂ ≠ 0`). -/
  assumeNonzeroAdd_sound :
    SoundBackwardRefine scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ ≠ 0) assumeNonzeroAdd
  /-- Backward refinement for addition under zero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ = 0`, refine both. -/
  assumeZeroAdd : A → A → A × A := fun a₁ a₂ => (a₁, a₂)
  /-- Zero-add backward refinement is sound (`SoundBackwardRefine` with
      `rel := fun v₁ v₂ => v₁ + v₂ = 0`). -/
  assumeZeroAdd_sound :
    SoundBackwardRefine scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ = 0) assumeZeroAdd

namespace IMPAnalysisDomain

variable {A : Type u} [Bot A] [Preorder A] [OrderTop A] [Max A]
variable (d : IMPAnalysisDomain A)

/-- Convenience accessor for the scalar concretization function. -/
abbrev gamma : A → Set Int := d.scalarDomain.gamma

/-- Convenience accessor for the scalar join (`⊔` from the `Max A` instance). -/
abbrev join : A → A → A := (· ⊔ ·)

/-- Convenience accessor for the scalar top element (from `OrderTop A`). -/
abbrev top : A := ⊤

end IMPAnalysisDomain

end Examples.IMP
