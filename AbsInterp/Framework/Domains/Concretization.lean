import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

import AbsInterp.Framework.Concretization

/-!
# Concretization Domain Interface

`ConcretizationDomain` packages the core γ-only soundness contract for abstract
domains: a concretization function `gamma` together with monotonicity and
top-coverage obligations. No abstraction function `α` or Galois-connection
obligation is required.

The abstract carrier is required to carry `[Preorder] [OrderTop]` instances. Join
soundness is derived generically when `[SemilatticeSup]` is available. An opt-in
`GaloisConnection` bridge for domains that do have an `α` lives in
`AbsInterp.Framework.Domains.Interop.GaloisConnection`.

## References

* P. Cousot, R. Cousot, *Abstract Interpretation: A Unified Lattice Model for
  Static Analysis of Programs by Construction or Approximation of Fixpoints*,
  POPL 1977. doi:10.1145/512950.512973
* X. Leroy, *Mechanizing abstract interpretation*,
  Workshop on the Next 40 years of Abstract Interpretation (N40AI), 2024.
  https://xavierleroy.org/talks/N40AI.pdf
-/

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-- Core concretization-domain contract. The contract pins down the γ-only obligations:

- `gamma` : the concretization function,
- `gamma_monotone` : `≤`-monotonicity of `gamma`,
- `gamma_top` : `⊤` over-approximates every concrete element.

This deliberately omits `α` / Galois-connection obligations. While
`SemilatticeSup` provides the abstract-level LUB laws, γ-level join soundness is
recovered as a generic theorem from monotonicity.
-/
structure ConcretizationDomain
    (Abstract : Type u) [Preorder Abstract] [OrderTop Abstract]
    (Concrete : Type v) where
  /-- The concretization function mapping abstract elements to concrete sets. -/
  gamma : Concretization Abstract Concrete
  gamma_monotone : ∀ ⦃a b : Abstract⦄, a ≤ b → gamma a ⊆ gamma b
  gamma_top : ∀ c : Concrete, c ∈ gamma ⊤

namespace ConcretizationDomain

theorem gamma_union_subset_sup
    {Abstract : Type u} [SemilatticeSup Abstract] [OrderTop Abstract]
    {Concrete : Type v}
    (cfg : ConcretizationDomain Abstract Concrete)
    (a b : Abstract) :
    cfg.gamma a ∪ cfg.gamma b ⊆ cfg.gamma (a ⊔ b) := by
  intro c hc
  rcases hc with ha | hb
  · exact cfg.gamma_monotone le_sup_left ha
  · exact cfg.gamma_monotone le_sup_right hb

end ConcretizationDomain

end Domains
end Framework
end AbsInterp
