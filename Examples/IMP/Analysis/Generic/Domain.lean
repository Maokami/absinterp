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

The interface sits between the scalar abstract domain (`ConcretizationDomain A Int`)
and the IMP-specific analysis machinery by bundling reusable framework
capabilities:

- bottom soundness,
- point abstraction of integer literals,
- sound addition transfer,
- a meet-like combinator used to combine same-variable backward refinements,
- branch filter operators,
- relational backward operators for addition tests.
-/

/--
Domain-specific obligations for a generic IMP abstract analysis.

An instance packages a scalar `ConcretizationDomain` together with the transfer
capabilities needed by the generic IMP transfer function and its soundness
proof.
-/
structure IMPAnalysisDomain
    (A : Type u) [Bot A] [SemilatticeSup A] [OrderTop A] where
  /-- The underlying scalar concretization domain over integers. -/
  scalarDomain : ConcretizationDomain A Int
  /-- The bottom element has empty concretization. -/
  bottom : BottomConcretization A scalarDomain.gamma
  /-- Point abstraction for integer literals. -/
  const : PointAbstraction A scalarDomain.gamma
  /-- Addition transfer. -/
  addTransfer : BinaryTransfer A scalarDomain.gamma (· + ·)
  /-- Combine two scalar refinements for the same concrete value. -/
  intersect : MeetLike A scalarDomain.gamma
  /-- Filter an abstract value under a nonzero assumption. -/
  filterNonzero : FilterOperator A scalarDomain.gamma (· ≠ 0)
  /-- Filter an abstract value under a zero assumption. -/
  filterZero : FilterOperator A scalarDomain.gamma (· = 0)
  /-- Backward operator for addition under nonzero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ ≠ 0`, refine both. -/
  backwardAddNonzero :
    RelationalBackwardOperator A scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ ≠ 0)
  /-- Backward operator for addition under zero constraint.
      Given `v₁ ∈ γ(a₁)`, `v₂ ∈ γ(a₂)`, and `v₁ + v₂ = 0`, refine both. -/
  backwardAddZero :
    RelationalBackwardOperator A scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ = 0)

namespace IMPAnalysisDomain

variable {A : Type u} [Bot A] [SemilatticeSup A] [OrderTop A]
variable (d : IMPAnalysisDomain A)

/-- Bottom soundness accessor. -/
theorem gamma_bot : d.scalarDomain.gamma ⊥ = ∅ :=
  d.bottom.gamma_bot

/-- Constant abstraction soundness accessor. -/
theorem const_sound (n : Int) :
    n ∈ d.scalarDomain.gamma (d.const n) :=
  d.const.sound n

/-- Addition-transfer soundness accessor. -/
theorem addTransfer_sound
    {a₁ a₂ : A} {v₁ v₂ : Int} :
    v₁ ∈ d.scalarDomain.gamma a₁ → v₂ ∈ d.scalarDomain.gamma a₂ →
    v₁ + v₂ ∈ d.scalarDomain.gamma (d.addTransfer a₁ a₂) :=
  d.addTransfer.sound

/-- Meet-like soundness accessor. -/
theorem intersect_sound
    {a₁ a₂ : A} {v : Int} :
    v ∈ d.scalarDomain.gamma a₁ → v ∈ d.scalarDomain.gamma a₂ →
    v ∈ d.scalarDomain.gamma (d.intersect a₁ a₂) :=
  d.intersect.sound

/-- Meet-like reductiveness accessor. -/
theorem intersect_reductive (a₁ a₂ : A) :
    d.intersect a₁ a₂ ≤ a₁ ∧ d.intersect a₁ a₂ ≤ a₂ :=
  d.intersect.reductive a₁ a₂

/-- Nonzero-filter soundness accessor. -/
theorem filterNonzero_sound :
    SoundFilter d.scalarDomain.gamma (· ≠ 0) d.filterNonzero :=
  d.filterNonzero.sound

/-- Nonzero-filter reductiveness accessor. -/
theorem filterNonzero_reductive :
    ReductiveFilter d.filterNonzero :=
  d.filterNonzero.reductive

/-- Zero-filter soundness accessor. -/
theorem filterZero_sound :
    SoundFilter d.scalarDomain.gamma (· = 0) d.filterZero :=
  d.filterZero.sound

/-- Zero-filter reductiveness accessor. -/
theorem filterZero_reductive :
    ReductiveFilter d.filterZero :=
  d.filterZero.reductive

/-- Nonzero-add backward-operator soundness accessor. -/
theorem backwardAddNonzero_sound :
    SoundBackwardOperator d.scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ ≠ 0) d.backwardAddNonzero :=
  d.backwardAddNonzero.sound

/-- Nonzero-add backward-operator reductiveness accessor. -/
theorem backwardAddNonzero_reductive :
    ReductiveBackwardOperator d.backwardAddNonzero :=
  d.backwardAddNonzero.reductive

/-- Zero-add backward-operator soundness accessor. -/
theorem backwardAddZero_sound :
    SoundBackwardOperator d.scalarDomain.gamma
      (fun v₁ v₂ => v₁ + v₂ = 0) d.backwardAddZero :=
  d.backwardAddZero.sound

/-- Zero-add backward-operator reductiveness accessor. -/
theorem backwardAddZero_reductive :
    ReductiveBackwardOperator d.backwardAddZero :=
  d.backwardAddZero.reductive

/-- Convenience accessor for the scalar concretization function. -/
abbrev gamma : A → Set Int := d.scalarDomain.gamma

/-- Convenience accessor for the scalar join (`⊔` from the `SemilatticeSup A` instance). -/
abbrev join : A → A → A := (· ⊔ ·)

/-- Convenience accessor for the scalar top element (from `OrderTop A`). -/
abbrev top : A := ⊤

end IMPAnalysisDomain

end Examples.IMP
