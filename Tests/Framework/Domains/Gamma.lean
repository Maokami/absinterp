import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkDomainsGamma

open AbsInterp
open AbsInterp.Domains

/-! ## Smoke tests: the γ-only domain contract

After the alignment with Mathlib `[Preorder] [OrderTop] [SemilatticeSup]`,
`≤`, `⊤`, and `⊔` come from typeclass instances rather than domain fields.
-/

example :
    (0 : Int) ∈
      Domains.signGammaDomain.gamma (⊤ : Sign) := by
  simpa using Domains.signGammaDomain.gamma_top 0

example :
    Domains.signGammaDomain.gamma Sign.neg ∪
      Domains.signGammaDomain.gamma Sign.zero ⊆
      Domains.signGammaDomain.gamma (Sign.neg ⊔ Sign.zero) := by
  simpa using Domains.signGammaDomain.join_sound Sign.neg Sign.zero

example :
    (3 : Int) ∈
      Domains.intervalGammaDomain.gamma (⊤ : Interval) := by
  simpa using Domains.intervalGammaDomain.gamma_top 3

example :
    Domains.intervalGammaDomain.gamma (Domains.mk 1 2) ∪
      Domains.intervalGammaDomain.gamma (Domains.mk 4 5) ⊆
      Domains.intervalGammaDomain.gamma
        (Domains.mk 1 2 ⊔ Domains.mk 4 5) := by
  simpa using
    Domains.intervalGammaDomain.join_sound (Domains.mk 1 2) (Domains.mk 4 5)

end FrameworkDomainsGamma
end Tests
