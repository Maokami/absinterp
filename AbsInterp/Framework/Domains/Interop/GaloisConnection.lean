import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Lattice

import AbsInterp.Framework.Domains.Gamma

/-!
# Galois-connection interop for `GammaDomain`

Opt-in bridge that builds a `GammaDomain` from a Mathlib
`GaloisConnection`. The core γ-only contract in
`AbsInterp.Framework.Domains.Gamma` deliberately avoids depending on
`α` or Galois connections; this module is kept separate so that users
who already have an `α : Set Concrete → Abstract` can reuse the
existing Galois-theoretic lemmas without polluting the γ-only module.
-/

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/--
Bridge: build a `GammaDomain` from a Mathlib `GaloisConnection` between
`Abstract` and `Set Concrete` (with subset order).

`α : Set Concrete → Abstract` is the abstraction map and `γ : Abstract → Set Concrete`
is the concretization. A `GaloisConnection α γ` automatically yields:

- γ-monotonicity (from `gc.monotone_u`),
- `c ∈ γ ⊤` for every `c` (from `α univ ≤ ⊤` and the Galois adjoint),
- soundness of `⊔` on the abstract side (from `α`'s preservation of binary
  unions, which requires `[SemilatticeSup Abstract]`).
-/
def GammaDomain.ofGaloisConnection
    {Abstract : Type u} [SemilatticeSup Abstract] [OrderTop Abstract]
    {Concrete : Type v}
    (gamma : Abstract → Set Concrete)
    (alpha : Set Concrete → Abstract)
    (gc : GaloisConnection alpha gamma) :
    GammaDomain Abstract Concrete where
  gamma := gamma
  gamma_monotone := gc.monotone_u
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
