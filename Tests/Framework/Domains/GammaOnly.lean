import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkDomainsGammaOnly

open AbsInterp
open AbsInterp.Domains

/-! ## Smoke tests: the γ-only domain contract

After the alignment with Mathlib `[Preorder] [OrderTop] [SemilatticeSup]`,
`≤`, `⊤`, and `⊔` come from typeclass instances rather than domain fields.
-/

example :
    (0 : Int) ∈
      Domains.signGammaOnlyDomain.gamma (⊤ : Sign) := by
  simpa using Domains.signGammaOnlyDomain.gamma_top 0

example :
    Domains.signGammaOnlyDomain.gamma Sign.neg ∪
      Domains.signGammaOnlyDomain.gamma Sign.zero ⊆
      Domains.signGammaOnlyDomain.gamma (Sign.neg ⊔ Sign.zero) := by
  simpa using Domains.signGammaOnlyDomain.join_sound Sign.neg Sign.zero

example :
    (3 : Int) ∈
      Domains.intervalGammaOnlyDomain.gamma (⊤ : Interval) := by
  simpa using Domains.intervalGammaOnlyDomain.gamma_top 3

example :
    Domains.intervalGammaOnlyDomain.gamma (Domains.mk 1 2) ∪
      Domains.intervalGammaOnlyDomain.gamma (Domains.mk 4 5) ⊆
      Domains.intervalGammaOnlyDomain.gamma
        (Domains.mk 1 2 ⊔ Domains.mk 4 5) := by
  simpa using
    Domains.intervalGammaOnlyDomain.join_sound (Domains.mk 1 2) (Domains.mk 4 5)

end FrameworkDomainsGammaOnly
end Tests
