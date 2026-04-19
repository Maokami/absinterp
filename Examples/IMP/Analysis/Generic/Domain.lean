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

The interface sits between the scalar abstract domain (`GammaDomain A Int`)
and the IMP-specific analysis machinery. A concrete instance must supply:

- scalar expression evaluation primitives (`const`, `addTransfer`) with
  soundness,
- branch filter operators (`filterNonzero`, `filterZero`) with soundness,
- a proof that the bottom element has empty concretization.
-/

/--
Domain-specific obligations for a generic IMP abstract analysis.

An instance packages a scalar `GammaDomain` together with the transfer
primitives and soundness contracts needed by the generic IMP transfer function
and its soundness proof.
-/
structure IMPAnalysisDomain
    (A : Type u) [Bot A] [Preorder A] [OrderTop A] [SemilatticeSup A] where
  /-- The underlying scalar gamma-only domain over integers. -/
  scalarDomain : GammaDomain A Int
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
  /-- Filter an abstract value under a nonzero assumption. -/
  filterNonzero : A → A
  /-- Nonzero filtering is sound (`SoundFilter` with `P := (· ≠ 0)`). -/
  filterNonzero_sound :
    SoundFilter scalarDomain.gamma (· ≠ 0) filterNonzero
  /-- Nonzero filtering does not enlarge the abstract value. -/
  filterNonzero_reductive :
    ReductiveFilter filterNonzero
  /-- Filter an abstract value under a zero assumption. -/
  filterZero : A → A
  /-- Zero filtering is sound (`SoundFilter` with `P := (· = 0)`). -/
  filterZero_sound :
    SoundFilter scalarDomain.gamma (· = 0) filterZero
  /-- Zero filtering does not enlarge the abstract value. -/
  filterZero_reductive :
    ReductiveFilter filterZero
  /-- Backward operator for addition under nonzero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ ≠ 0`, refine both. -/
  backwardAddNonzero : BackwardOperator A := fun a₁ a₂ => (a₁, a₂)
  /-- Nonzero-add backward operator is sound. -/
  backwardAddNonzero_sound :
    SoundBackwardOperator scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ ≠ 0) backwardAddNonzero
  /-- Nonzero-add backward operator is reductive. -/
  backwardAddNonzero_reductive :
    ReductiveBackwardOperator backwardAddNonzero :=
      by
        intro a₁ a₂
        exact ⟨le_rfl, le_rfl⟩
  /-- Backward operator for addition under zero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ = 0`, refine both. -/
  backwardAddZero : BackwardOperator A := fun a₁ a₂ => (a₁, a₂)
  /-- Zero-add backward operator is sound. -/
  backwardAddZero_sound :
    SoundBackwardOperator scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ = 0) backwardAddZero
  /-- Zero-add backward operator is reductive. -/
  backwardAddZero_reductive :
    ReductiveBackwardOperator backwardAddZero :=
      by
        intro a₁ a₂
        exact ⟨le_rfl, le_rfl⟩

namespace IMPAnalysisDomain

variable {A : Type u} [Bot A] [Preorder A] [OrderTop A] [SemilatticeSup A]
variable (d : IMPAnalysisDomain A)

/-- Convenience accessor for the scalar concretization function. -/
abbrev gamma : A → Set Int := d.scalarDomain.gamma

/-- Convenience accessor for the scalar join (`⊔` from the `SemilatticeSup A` instance). -/
abbrev join : A → A → A := (· ⊔ ·)

/-- Convenience accessor for the scalar top element (from `OrderTop A`). -/
abbrev top : A := ⊤

end IMPAnalysisDomain

end Examples.IMP
