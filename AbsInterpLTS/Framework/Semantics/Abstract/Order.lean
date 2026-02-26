import Cslib.Init
import Mathlib.Order.Monotone.Defs

import AbsInterpLTS.Framework.Semantics.Abstract.Defs

namespace AbsInterpLTS
namespace Framework

universe u

section Basic

variable {Abstract : Type u}
variable [Preorder Abstract]

/-- Monotonicity predicate for abstract transformers over a preorder. -/
def MonotonePostSharp (postSharp : PostSharp Abstract) : Prop :=
  Monotone postSharp

/-- The identity abstract transformer is monotone. -/
theorem MonotonePostSharp.id :
    MonotonePostSharp (fun a : Abstract => a) := by
  intro a b hAB
  exact hAB

/-- Composition of monotone abstract transformers is monotone. -/
theorem MonotonePostSharp.compose
    {postSharp1 postSharp2 : PostSharp Abstract}
    (h1 : MonotonePostSharp postSharp1)
    (h2 : MonotonePostSharp postSharp2) :
    MonotonePostSharp (composePostSharp postSharp1 postSharp2) := by
  intro a b hAB
  exact h2 (h1 hAB)

end Basic

end Framework
end AbsInterpLTS
