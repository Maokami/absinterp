import Cslib.Init

import AbsInterpLTS.Framework.Semantics.Concrete.Defs

namespace AbsInterpLTS
namespace Framework

universe u

/--
Monotone one-step collecting semantics packaged as a reusable interface.
-/
structure CollectingStep (State : Type u) where
  post : Post State
  monotone : MonotonePost post

namespace CollectingStep

/--
Collecting-style fixpoint operator for reachability:
`reachF init states = init ∪ post states`.
-/
def reachF
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) :
    Post State :=
  fun states => init ∪ cfg.post states

end CollectingStep

end Framework
end AbsInterpLTS
