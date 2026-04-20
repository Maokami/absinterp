import Cslib.Init

import AbsInterp

namespace Tests
namespace DomainsParity

open AbsInterp
open AbsInterp.Domains

example : (4 : Int) ∈ gammaParity (intersectParity Parity.top Parity.even) := by
  exact intersectParity_sound (by simp [gammaParity]) (by simp [gammaParity])

example : intersectParity Parity.even Parity.odd = Parity.bot := by
  rfl

end DomainsParity
end Tests
