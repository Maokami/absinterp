import Cslib.Init

import AbsInterp.Framework.Iteration.Widening.Defs
import AbsInterp.Framework.Iteration.Fixpoint.Defs

namespace AbsInterp
namespace Framework
namespace Iteration

open AbsInterp.Framework

universe u

/-- `witer` returns a post-fixpoint of `f`. -/
theorem isPostFixpoint_witer
    {Abstract : Type u}
    {le : Abstract -> Abstract -> Prop}
    {f : Abstract -> Abstract}
    {widen : Widen Abstract}
    (le_dec : ∀ a b : Abstract, Decidable (le a b))
    (hWiden : WidenUpperBound le widen)
    {x y : Abstract}
    (hLe : le x y)
    (acc : WAcc le f widen x y) :
    IsPostFixpoint le f (witer le_dec hWiden hLe acc) := by
  match acc with
  | .intro _ _ ih_acc =>
    simp [witer]
    split
    case isTrue h => exact h
    case isFalse h =>
      exact isPostFixpoint_witer le_dec hWiden
        (hWiden.right y (f y)) (ih_acc hLe h)

/-- `pfp` returns a post-fixpoint of `f`. -/
theorem isPostFixpoint_pfp
    {Abstract : Type u}
    {le : Abstract -> Abstract -> Prop}
    {f : Abstract -> Abstract}
    {widen : Widen Abstract}
    (le_dec : ∀ a b : Abstract, Decidable (le a b))
    (hWiden : WidenUpperBound le widen)
    (bot : Abstract)
    (hBot : ∀ a : Abstract, le bot a)
    (acc : WAcc le f widen bot bot) :
    IsPostFixpoint le f (pfp le_dec hWiden bot hBot acc) :=
  isPostFixpoint_witer le_dec hWiden (hBot bot) acc

end Iteration
end Framework
end AbsInterp
