import Cslib.Init

namespace AbsInterpLTS
namespace Framework
namespace Domains

universe u v

/-- Concretization map from abstract elements to concrete sets. -/
abbrev Gamma (Abstract : Type u) (Concrete : Type v) := Abstract -> Set Concrete

/--
`gamma`-only abstract-domain contract.

This interface fixes the minimal obligations used by the current framework:
order (`le`), concretization monotonicity, top coverage, and join soundness.
It intentionally does not include `alpha` or Galois-connection fields.
-/
structure GammaOnlyDomain (Abstract : Type u) (Concrete : Type v) where
  gamma : Gamma Abstract Concrete
  le : Abstract -> Abstract -> Prop
  le_refl : ∀ a : Abstract, le a a
  le_trans : ∀ {a b c : Abstract}, le a b -> le b c -> le a c
  gamma_monotone : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b
  top : Abstract
  gamma_top : ∀ c : Concrete, c ∈ gamma top
  join : Abstract -> Abstract -> Abstract
  join_sound :
    ∀ a b : Abstract, gamma a ∪ gamma b ⊆ gamma (join a b)

namespace GammaOnlyDomain

variable {Abstract : Type u} {Concrete : Type v}
variable (cfg : GammaOnlyDomain Abstract Concrete)

/-- The order relation carried by a `GammaOnlyDomain`. -/
abbrev LE : Abstract -> Abstract -> Prop :=
  cfg.le

/-- Concretization monotonicity as a named theorem. -/
theorem gamma_monotone_of_le {a b : Abstract} (h : cfg.le a b) :
    cfg.gamma a ⊆ cfg.gamma b :=
  cfg.gamma_monotone h

/-- Every concrete element is in the concretization of `top`. -/
theorem mem_gamma_top (c : Concrete) :
    c ∈ cfg.gamma cfg.top :=
  cfg.gamma_top c

/-- Join is sound w.r.t. concretization union. -/
theorem gamma_union_subset_join (a b : Abstract) :
    cfg.gamma a ∪ cfg.gamma b ⊆ cfg.gamma (cfg.join a b) :=
  cfg.join_sound a b

end GammaOnlyDomain

end Domains
end Framework
end AbsInterpLTS
