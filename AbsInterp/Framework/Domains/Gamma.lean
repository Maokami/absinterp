import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Lattice

/-!
# Gamma-Only Abstract Domain Interface

`GammaDomain` packages the γ-only soundness contract for abstract domains:
a concretization function `gamma` together with monotonicity, top-coverage, and
join-soundness obligations. No abstraction function `α` or Galois-connection
obligation is required.

The abstract carrier is required to carry `[Preorder] [OrderTop] [SemilatticeSup]`
Mathlib instances. `[SemilatticeSup]` subsumes `[Max]` via `SemilatticeSup.toMax`,
so the join `⊔` is available uniformly. An opt-in `GaloisConnection` bridge for
domains that do have an `α` lives in
`AbsInterp.Framework.Domains.Gamma.Interop`.

## References

* P. Cousot, R. Cousot, *Abstract Interpretation: A Unified Lattice Model for
  Static Analysis of Programs by Construction or Approximation of Fixpoints*,
  POPL 1977. doi:10.1145/512950.512973
* X. Leroy, *Semantics and Verification of Computer Programs*,
  MPRI lecture notes (N40AI), 2023–2024.
-/

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-- Concretization map from abstract elements to concrete sets. -/
abbrev Gamma (Abstract : Type u) (Concrete : Type v) := Abstract -> Set Concrete

/--
`gamma`-only abstract-domain contract.

The abstract carrier is a Mathlib-style ordered join-semilattice with a top
element (`Preorder + OrderTop + SemilatticeSup`). The contract pins down the
γ-only obligations:

- `gamma` : the concretization function,
- `gamma_monotone` : `≤`-monotonicity of `gamma`,
- `gamma_top` : `⊤` over-approximates every concrete element,
- `join_sound` : `⊔` soundly over-approximates concrete unions.

This deliberately omits `α` / Galois-connection obligations. While
`SemilatticeSup` already provides the abstract-level LUB laws
(`le_sup_left`, `le_sup_right`, `sup_le`), the γ-level `join_sound` is a
separate semantic soundness statement that the framework explicitly
requires.
-/
structure GammaDomain
    (Abstract : Type u) [Preorder Abstract] [OrderTop Abstract] [SemilatticeSup Abstract]
    (Concrete : Type v) where
  /-- The concretization function mapping abstract elements to concrete sets. -/
  gamma : Gamma Abstract Concrete
  gamma_monotone : ∀ ⦃a b : Abstract⦄, a ≤ b → gamma a ⊆ gamma b
  gamma_top : ∀ c : Concrete, c ∈ gamma ⊤
  join_sound : ∀ a b : Abstract, gamma a ∪ gamma b ⊆ gamma (a ⊔ b)

end Domains
end Framework
end AbsInterp
