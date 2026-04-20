import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic

import AbsInterp.Framework.Concretization

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-!
# Domain Capabilities

Small reusable capabilities that sit above the semantic `ConcretizationDomain`
kernel and below language-specific analysis adapters.

These structures intentionally avoid forcing full lattice structure. They encode
the minimum contracts needed by consumers such as generic IMP analyses.
-/

/-- A bottom element whose concretization is empty. -/
structure BottomConcretization
    (Abstract : Type u) [Bot Abstract]
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete) where
  gamma_bot : gamma ⊥ = ∅

/-- Point abstraction of concrete values into the abstract domain. -/
structure PointAbstraction
    (Abstract : Type u)
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete) where
  point : Concrete → Abstract
  sound : ∀ c : Concrete, c ∈ gamma (point c)

instance
    {Abstract : Type u}
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete} :
    CoeFun (PointAbstraction Abstract (gamma := gamma))
      (fun _ => Concrete → Abstract) where
  coe pointAbstraction := pointAbstraction.point

/--
A meet-like combinator that preserves common concrete witnesses and is
reductive in both arguments.

This is intentionally weaker than requiring a `SemilatticeInf`.
-/
def SoundMeetLike
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (meetLike : Abstract → Abstract → Abstract) : Prop :=
  ∀ {a₁ a₂ : Abstract} {c : Concrete},
    c ∈ gamma a₁ → c ∈ gamma a₂ → c ∈ gamma (meetLike a₁ a₂)

/-- A meet-like operator is reductive when it stays below both inputs. -/
def ReductiveMeetLike
    {Abstract : Type u} [Preorder Abstract]
    (meetLike : Abstract → Abstract → Abstract) : Prop :=
  ∀ a₁ a₂ : Abstract, meetLike a₁ a₂ ≤ a₁ ∧ meetLike a₁ a₂ ≤ a₂

structure MeetLike
    (Abstract : Type u) [Preorder Abstract]
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete) where
  meetLike : Abstract → Abstract → Abstract
  sound : SoundMeetLike gamma meetLike
  reductive : ReductiveMeetLike meetLike

instance
    {Abstract : Type u} [Preorder Abstract]
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete} :
    CoeFun (MeetLike Abstract (gamma := gamma))
      (fun _ => Abstract → Abstract → Abstract) where
  coe meetLike := meetLike.meetLike

end Domains
end Framework
end AbsInterp
