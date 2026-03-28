import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkDomainsGammaOnly

open AbsInterp
open AbsInterp.Domains

example :
    (0 : Int) ∈
      Domains.signGammaOnlyDomain.gamma Domains.signGammaOnlyDomain.top := by
  simpa using Domains.signGammaOnlyDomain.gamma_top 0

example :
    Domains.signGammaOnlyDomain.gamma Sign.neg ∪
      Domains.signGammaOnlyDomain.gamma Sign.zero ⊆
      Domains.signGammaOnlyDomain.gamma
        (Domains.signGammaOnlyDomain.join Sign.neg Sign.zero) := by
  simpa using Domains.signGammaOnlyDomain.join_sound Sign.neg Sign.zero

example :
    (3 : Int) ∈
      Domains.intervalGammaOnlyDomain.gamma Domains.intervalGammaOnlyDomain.top := by
  simpa using Domains.intervalGammaOnlyDomain.gamma_top 3

example :
    Domains.intervalGammaOnlyDomain.gamma (Domains.mk 1 2) ∪
      Domains.intervalGammaOnlyDomain.gamma (Domains.mk 4 5) ⊆
      Domains.intervalGammaOnlyDomain.gamma
        (Domains.intervalGammaOnlyDomain.join (Domains.mk 1 2) (Domains.mk 4 5)) := by
  simpa using
    Domains.intervalGammaOnlyDomain.join_sound (Domains.mk 1 2) (Domains.mk 4 5)

end FrameworkDomainsGammaOnly
end Tests
