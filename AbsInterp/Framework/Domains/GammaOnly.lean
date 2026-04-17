import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Lattice

/-!
# Gamma-Only Abstract Domain Interface

`GammaOnlyDomain` packages the γ-only soundness contract for abstract domains:
a concretization function `gamma` together with monotonicity, top-coverage, and
join-soundness obligations. No abstraction function `α` or Galois-connection
obligation is required.

The abstract carrier is required to carry `[Preorder] [OrderTop] [Max]` Mathlib
instances. Domains that additionally satisfy `[SemilatticeSup]` may provide it
as an opt-in instance. `GammaOnlyDomain.ofGaloisConnection` bridges the γ-only
interface with the standard Mathlib `GaloisConnection` for domains that do have
an `α`.

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

The abstract carrier is a Mathlib-style ordered type with a top element and a
binary `⊔` operation (`Preorder + OrderTop + Max`). The contract pins down the
γ-only obligations:

- `gamma` : the concretization function,
- `gamma_monotone` : `≤`-monotonicity of `gamma`,
- `gamma_top` : `⊤` over-approximates every concrete element,
- `join_sound` : `⊔` soundly over-approximates concrete unions.

This deliberately omits `α` / Galois-connection / abstract-level LUB
obligations. The `Max` typeclass carries no laws on its own; the only join
law required here is the γ-level `join_sound`. Domains that additionally
satisfy `SemilatticeSup` are welcome to provide it as an opt-in instance.
-/
structure GammaOnlyDomain
    (Abstract : Type u) [Preorder Abstract] [OrderTop Abstract] [Max Abstract]
    (Concrete : Type v) where
  /-- The concretization function mapping abstract elements to concrete sets. -/
  gamma : Gamma Abstract Concrete
  gamma_monotone : ∀ {a b : Abstract}, a ≤ b → gamma a ⊆ gamma b
  gamma_top : ∀ c : Concrete, c ∈ gamma ⊤
  join_sound : ∀ a b : Abstract, gamma a ∪ gamma b ⊆ gamma (a ⊔ b)

namespace GammaOnlyDomain

variable {Abstract : Type u} [Preorder Abstract] [OrderTop Abstract] [Max Abstract]
variable {Concrete : Type v}
variable (cfg : GammaOnlyDomain Abstract Concrete)

/-- Concretization monotonicity as a named theorem. -/
theorem gamma_monotone_of_le {a b : Abstract} (h : a ≤ b) :
    cfg.gamma a ⊆ cfg.gamma b :=
  cfg.gamma_monotone h

/-- Every concrete element is in the concretization of `⊤`. -/
theorem mem_gamma_top (c : Concrete) :
    c ∈ cfg.gamma (⊤ : Abstract) :=
  cfg.gamma_top c

/-- Join is sound w.r.t. concretization union. -/
theorem gamma_union_subset_join (a b : Abstract) :
    cfg.gamma a ∪ cfg.gamma b ⊆ cfg.gamma (a ⊔ b) :=
  cfg.join_sound a b

end GammaOnlyDomain

/--
Bridge: build a `GammaOnlyDomain` from a Mathlib `GaloisConnection` between
`Abstract` and `Set Concrete` (with subset order).

`α : Set Concrete → Abstract` is the abstraction map and `γ : Abstract → Set Concrete`
is the concretization. A `GaloisConnection α γ` automatically yields:

- γ-monotonicity (from `gc.monotone_u`),
- `c ∈ γ ⊤` for every `c` (from `α univ ≤ ⊤` and the Galois adjoint),
- soundness of `⊔` on the abstract side (from `α`'s preservation of binary
  unions, which requires `[SemilatticeSup Abstract]`).

This helper is opt-in; the framework does not require a `GaloisConnection`
to use γ-only soundness.
-/
def GammaOnlyDomain.ofGaloisConnection
    {Abstract : Type u} [SemilatticeSup Abstract] [OrderTop Abstract]
    {Concrete : Type v}
    (gamma : Abstract → Set Concrete)
    (alpha : Set Concrete → Abstract)
    (gc : GaloisConnection alpha gamma) :
    GammaOnlyDomain Abstract Concrete where
  gamma := gamma
  gamma_monotone := @(gc.monotone_u)
  gamma_top := by
    intro c
    have hLeTop : alpha Set.univ ≤ (⊤ : Abstract) := le_top
    exact (gc _ _).mp hLeTop (Set.mem_univ c)
  join_sound := by
    intro a b
    have hsup : alpha (gamma a ∪ gamma b) ≤ a ⊔ b := by
      have ha : alpha (gamma a) ≤ a := gc.l_u_le a
      have hb : alpha (gamma b) ≤ b := gc.l_u_le b
      calc alpha (gamma a ∪ gamma b)
          = alpha (gamma a) ⊔ alpha (gamma b) := gc.l_sup
        _ ≤ a ⊔ b := sup_le_sup ha hb
    exact (gc _ _).mp hsup

end Domains
end Framework
end AbsInterp
#lint
