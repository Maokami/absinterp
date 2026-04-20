import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.BooleanAlgebra.Set

import AbsInterp.Framework.Domains.Concretization

/-!
# Galois-connection interop for `ConcretizationDomain`

Opt-in bridge that builds a `ConcretizationDomain` from a Mathlib
`GaloisConnection`. The core γ-only contract in
`AbsInterp.Framework.Domains.Concretization` deliberately avoids depending on
`α` or Galois connections; this module is kept separate so that users
who already have an `α : Set Concrete → Abstract` can reuse the
existing Galois-theoretic lemmas without polluting the γ-only module.
-/

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/--
Bridge: build a `ConcretizationDomain` from a Mathlib `GaloisConnection` between
`Abstract` and `Set Concrete` (with subset order).

`α : Set Concrete → Abstract` is the abstraction map and `γ : Abstract → Set Concrete`
is the concretization. A `GaloisConnection α γ` automatically yields:

- γ-monotonicity (from `gc.monotone_u`),
- `c ∈ γ ⊤` for every `c` (from `α univ ≤ ⊤` and the Galois adjoint).
-/
def ConcretizationDomain.ofGaloisConnection
    {Abstract : Type u} [Preorder Abstract] [OrderTop Abstract]
    {Concrete : Type v}
    (gamma : Abstract → Set Concrete)
    (alpha : Set Concrete → Abstract)
    (gc : GaloisConnection alpha gamma) :
    ConcretizationDomain Abstract Concrete where
  gamma := gamma
  gamma_monotone := gc.monotone_u
  gamma_top := by
    intro c
    have hLeTop : alpha Set.univ ≤ (⊤ : Abstract) := le_top
    exact (gc _ _).mp hLeTop (Set.mem_univ c)

end Domains
end Framework
end AbsInterp
