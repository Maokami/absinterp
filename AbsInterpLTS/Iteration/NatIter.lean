import Cslib.Init

import AbsInterpLTS.Core.Semantics

namespace AbsInterpLTS
namespace Iteration

open AbsInterpLTS.Core

universe u

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

/-- Natural-number iterate scaffold for concrete post operators. -/
def iterateNat
    {State : Type u}
    (post : Post State)
    (init : Set State) :
    Nat -> Set State
  | 0 => init
  | n + 1 => post (iterateNat post init n)

end Iteration
end AbsInterpLTS
