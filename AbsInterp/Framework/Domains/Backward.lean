import Cslib.Init

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-!
# Backward Abstract Operators

Generic backward (refinement) operator types and soundness predicates,
following the gamma-only approach.

Backward operators refine abstract values given relational knowledge about
their concretizations:

- **Unary assume**: refine `a` given a property `P` of the concrete value.
- **Binary backward refinement**: refine a pair `(a₁, a₂)` given a relational
  constraint between their concrete values (N40AI slide 6 style).
-/

/--
Soundness of a unary backward refinement (assume) operator.

If `c ∈ γ(a)` and the property `P c` holds, then `c ∈ γ(assume a)`.

The existing `assumeNonzero` / `assumeZero` operators in concrete domains
are instances of this pattern.
-/
def SoundAssume
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Abstract → Set Concrete)
    (P : Concrete → Prop)
    (assume_ : Abstract → Abstract) : Prop :=
  ∀ (a : Abstract) (c : Concrete),
    c ∈ gamma a → P c → c ∈ gamma (assume_ a)

/--
Soundness of a binary backward refinement operator (N40AI-style).

Given `refine : A → A → A × A`, soundness means: if `c₁ ∈ γ(a₁)`,
`c₂ ∈ γ(a₂)`, and the relational constraint `rel c₁ c₂` holds, then
`c₁ ∈ γ((refine a₁ a₂).1)` and `c₂ ∈ γ((refine a₁ a₂).2)`.

This matches Leroy's N40AI backward operator formulation:
`(a'₁, a'₂) = (a₁ op⁻¹♯ a₂)` means
`v₁ ∈ γ(a₁) ∧ v₂ ∈ γ(a₂) ∧ v₁ op v₂ ⇒ v₁ ∈ γ(a'₁) ∧ v₂ ∈ γ(a'₂)`.
-/
def SoundBackwardRefine
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Abstract → Set Concrete)
    (rel : Concrete → Concrete → Prop)
    (refine : Abstract → Abstract → Abstract × Abstract) : Prop :=
  ∀ (a₁ a₂ : Abstract) (c₁ c₂ : Concrete),
    c₁ ∈ gamma a₁ → c₂ ∈ gamma a₂ → rel c₁ c₂ →
    c₁ ∈ gamma (refine a₁ a₂).1 ∧ c₂ ∈ gamma (refine a₁ a₂).2

/-- The identity backward refinement is trivially sound for any relation. -/
theorem soundBackwardRefine_id
    {Abstract : Type u} {Concrete : Type v}
    {gamma : Abstract → Set Concrete}
    {rel : Concrete → Concrete → Prop} :
    SoundBackwardRefine gamma rel (fun a₁ a₂ => (a₁, a₂)) :=
  fun _ _ _ _ h₁ h₂ _ => ⟨h₁, h₂⟩

/-!
## Usage note

These predicates are framework-level abstractions intended for reuse across
different language instantiations. The current IMP layer
(`Examples/IMP/Analysis/Generic/Domain.lean`) restates equivalent contracts
inline as `IMPAnalysisDomain` structure fields. A future refactor may wire
the IMP fields through these predicates directly.
-/

end Domains
end Framework
end AbsInterp
