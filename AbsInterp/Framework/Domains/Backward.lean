import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic

import AbsInterp.Framework.Concretization

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-!
# Backward Abstract Operators

Generic backward operator types and soundness predicates, following the
gamma-only approach.

Backward operators filter abstract values given relational knowledge about
their concretizations:

- **Unary filter**: filter `a` given a property `P` of the concrete value.
- **Binary backward operator**: filter a pair `(a₁, a₂)` given a relational
  constraint between their concrete values (N40AI slide 6 style).

## References

* P. Cousot, R. Cousot, *Abstract Interpretation: A Unified Lattice Model for
  Static Analysis of Programs by Construction or Approximation of Fixpoints*,
  POPL 1977. doi:10.1145/512950.512973
* X. Leroy, *Semantics and Verification of Computer Programs*,
  MPRI lecture notes (N40AI), 2023–2024, slides 6–8 (backward operators).
-/

/-- Binary backward operators simultaneously refine two abstract values. -/
abbrev BackwardOperator (Abstract : Type u) :=
  Abstract → Abstract → Abstract × Abstract

/--
Soundness of a unary filter operator.

If `c ∈ γ(a)` and the property `P c` holds, then `c ∈ γ(filter a)`.
-/
def SoundFilter
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (P : Concrete → Prop)
    (filter : Abstract → Abstract) : Prop :=
  ∀ {a : Abstract} {c : Concrete},
    c ∈ gamma a → P c → c ∈ gamma (filter a)

/-- A unary filter is reductive when it never enlarges its input. -/
def ReductiveFilter
    {Abstract : Type u} [Preorder Abstract]
    (filter : Abstract → Abstract) : Prop :=
  ∀ a : Abstract, filter a ≤ a

/--
Soundness of a binary backward operator (N40AI-style).

Given `backward : A → A → A × A`, soundness means: if `c₁ ∈ γ(a₁)`,
`c₂ ∈ γ(a₂)`, and the relational constraint `rel c₁ c₂` holds, then
`c₁ ∈ γ((backward a₁ a₂).1)` and `c₂ ∈ γ((backward a₁ a₂).2)`.

This matches Leroy's N40AI backward operator formulation:
`(a'₁, a'₂) = (a₁ op⁻¹♯ a₂)` means
`v₁ ∈ γ(a₁) ∧ v₂ ∈ γ(a₂) ∧ v₁ op v₂ ⇒ v₁ ∈ γ(a'₁) ∧ v₂ ∈ γ(a'₂)`.
-/
def SoundBackwardOperator
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (rel : Concrete → Concrete → Prop)
    (backward : BackwardOperator Abstract) : Prop :=
  ∀ {a₁ a₂ : Abstract} {c₁ c₂ : Concrete},
    c₁ ∈ gamma a₁ → c₂ ∈ gamma a₂ → rel c₁ c₂ →
    c₁ ∈ gamma (backward a₁ a₂).1 ∧ c₂ ∈ gamma (backward a₁ a₂).2

/--
A binary backward operator is reductive when each output stays below the
corresponding input.
-/
def ReductiveBackwardOperator
    {Abstract : Type u} [Preorder Abstract]
    (backward : BackwardOperator Abstract) : Prop :=
  ∀ a₁ a₂ : Abstract,
    (backward a₁ a₂).1 ≤ a₁ ∧ (backward a₁ a₂).2 ≤ a₂

/-- Bundled unary filter operator with soundness and reductiveness proofs. -/
structure FilterOperator
    (Abstract : Type u) [Preorder Abstract]
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (P : Concrete → Prop) where
  operator : Abstract → Abstract
  sound : SoundFilter gamma P operator
  reductive : ReductiveFilter operator

instance
    {Abstract : Type u} [Preorder Abstract]
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {P : Concrete → Prop} :
    CoeFun (FilterOperator Abstract (gamma := gamma) P)
      (fun _ => Abstract → Abstract) where
  coe filterOperator := filterOperator.operator

/--
Bundled binary backward operator with soundness and reductiveness proofs.

This is the bundled capability form of `BackwardOperator`.
-/
structure RelationalBackwardOperator
    (Abstract : Type u) [Preorder Abstract]
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (rel : Concrete → Concrete → Prop) where
  operator : BackwardOperator Abstract
  sound : SoundBackwardOperator gamma rel operator
  reductive : ReductiveBackwardOperator operator

instance
    {Abstract : Type u} [Preorder Abstract]
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {rel : Concrete → Concrete → Prop} :
    CoeFun (RelationalBackwardOperator Abstract (gamma := gamma) rel)
      (fun _ => Abstract → Abstract → Abstract × Abstract) where
  coe backwardOperator := backwardOperator.operator

namespace ReductiveFilter

/-- The identity filter is reductive. -/
theorem id
    {Abstract : Type u} [Preorder Abstract] :
    ReductiveFilter (fun a : Abstract => a) :=
  fun _ => le_rfl

end ReductiveFilter

namespace FilterOperator

/-- The identity filter operator is sound and reductive for any property. -/
def id
    {Abstract : Type u} [Preorder Abstract]
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {P : Concrete → Prop} :
    FilterOperator Abstract (gamma := gamma) P where
  operator := fun a => a
  sound := by
    intro a c hc _
    exact hc
  reductive := ReductiveFilter.id

end FilterOperator

namespace SoundBackwardOperator

/-- The identity backward operator is trivially sound for any relation. -/
theorem id
    {Abstract : Type u} {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {rel : Concrete → Concrete → Prop} :
    SoundBackwardOperator gamma rel (fun a₁ a₂ => (a₁, a₂)) :=
  fun h₁ h₂ _ => ⟨h₁, h₂⟩

end SoundBackwardOperator

namespace ReductiveBackwardOperator

/-- The identity backward operator is reductive. -/
theorem id
    {Abstract : Type u} [Preorder Abstract] :
    ReductiveBackwardOperator (fun a₁ a₂ : Abstract => (a₁, a₂)) :=
  fun _ _ => ⟨le_rfl, le_rfl⟩

end ReductiveBackwardOperator

namespace RelationalBackwardOperator

/-- The identity backward operator bundle is sound and reductive. -/
def id
    {Abstract : Type u} [Preorder Abstract]
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {rel : Concrete → Concrete → Prop} :
    RelationalBackwardOperator Abstract (gamma := gamma) rel where
  operator := fun a₁ a₂ => (a₁, a₂)
  sound := SoundBackwardOperator.id
  reductive := ReductiveBackwardOperator.id

end RelationalBackwardOperator

/-!
## Usage note

These predicates are the canonical contract for unary filters and binary
backward operators. `Examples/IMP/Analysis/Generic/Domain.lean` wires the
`IMPAnalysisDomain` filter and backward-operator fields through the bundled
`FilterOperator` and `RelationalBackwardOperator` capabilities, whose proof
fields are still expressed with `SoundFilter`, `ReductiveFilter`,
`SoundBackwardOperator`, and `ReductiveBackwardOperator`.
-/

end Domains
end Framework
end AbsInterp
