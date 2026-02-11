import Cslib.Init

import AbsInterpLTS.Core.Semantics

namespace AbsInterpLTS
namespace Core

universe u v

abbrev Gamma (Abstract : Type u) (State : Type v) := Abstract -> Set State
abbrev PostAbs (Abstract : Type u) := Abstract -> Abstract

/--
Core soundness direction used in this project:
`Post (gamma a) ⊆ gamma (PostAbs a)`.
-/
def Sound
    {State : Type u}
    {Abstract : Type v}
    (post : Post State)
    (gamma : Gamma Abstract State)
    (postAbs : PostAbs Abstract) : Prop :=
  forall a : Abstract, post (gamma a) ⊆ gamma (postAbs a)

end Core
end AbsInterpLTS
