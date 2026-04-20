import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkDomainsConcretization

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework.Domains

/-! ## Smoke tests: the concretization-domain contract

Join soundness is now a generic theorem derived from monotonicity rather than a
field carried by the domain structure.
-/

example :
    (0 : Int) ∈
      Domains.signConcretizationDomain.gamma (⊤ : Sign) := by
  simpa using Domains.signConcretizationDomain.gamma_top 0

example :
    Domains.signConcretizationDomain.gamma Sign.neg ∪
      Domains.signConcretizationDomain.gamma Sign.zero ⊆
      Domains.signConcretizationDomain.gamma (Sign.neg ⊔ Sign.zero) := by
  simpa using
    ConcretizationDomain.gamma_union_subset_sup
      Domains.signConcretizationDomain Sign.neg Sign.zero

example :
    (3 : Int) ∈
      Domains.intervalConcretizationDomain.gamma (⊤ : Interval) := by
  simpa using Domains.intervalConcretizationDomain.gamma_top 3

example :
    Domains.intervalConcretizationDomain.gamma (Domains.mk 1 2) ∪
      Domains.intervalConcretizationDomain.gamma (Domains.mk 4 5) ⊆
      Domains.intervalConcretizationDomain.gamma
        (Domains.mk 1 2 ⊔ Domains.mk 4 5) := by
  simpa using
    ConcretizationDomain.gamma_union_subset_sup
      Domains.intervalConcretizationDomain (Domains.mk 1 2) (Domains.mk 4 5)

end FrameworkDomainsConcretization
end Tests
