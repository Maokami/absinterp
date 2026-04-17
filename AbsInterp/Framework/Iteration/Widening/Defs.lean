import Init.SizeOf

namespace AbsInterp
namespace Framework
namespace Iteration

universe u

/-- Widening interface for abstract iterative solvers. -/
abbrev Widen (Abstract : Type u) := Abstract -> Abstract -> Abstract

/-- Narrowing interface for abstract iterative solvers. -/
abbrev Narrow (Abstract : Type u) := Abstract -> Abstract -> Abstract

/-- Post-fixpoint property: `f(a) ⊑ a`. -/
def IsPostFixpoint
    {Abstract : Type u}
    (le : Abstract -> Abstract -> Prop)
    (f : Abstract -> Abstract)
    (a : Abstract) : Prop :=
  le (f a) a

/-- Widening upper-bound contract: `widen a b` is above both `a` and `b`. -/
structure WidenUpperBound
    {Abstract : Type u}
    (le : Abstract -> Abstract -> Prop)
    (widen : Widen Abstract) : Prop where
  left : ∀ a b, le a (widen a b)
  right : ∀ a b, le b (widen a b)

/-- Widened accessibility predicate (N40AI WAcc).
    Constructive termination witness for widened iteration.
    `WAcc le f widen x y` means: starting from `x ⊑ y`,
    any widened chain reaches a post-fixpoint in finitely many steps. -/
inductive WAcc
    {Abstract : Type u}
    (le : Abstract -> Abstract -> Prop)
    (f : Abstract -> Abstract)
    (widen : Widen Abstract) :
    Abstract -> Abstract -> Type u where
  | intro : ∀ x y,
      (le x y ->
       ¬ le (f y) y ->
       WAcc le f widen (f y) (widen y (f y))) ->
      WAcc le f widen x y

/-- Widened iteration: computes post-fixpoint by structural recursion on WAcc. -/
def witer
    {Abstract : Type u}
    {le : Abstract -> Abstract -> Prop}
    {f : Abstract -> Abstract}
    {widen : Widen Abstract}
    (le_dec : ∀ a b : Abstract, Decidable (le a b))
    (hWiden : WidenUpperBound le widen)
    {x y : Abstract}
    (hLe : le x y)
    (acc : WAcc le f widen x y) : Abstract :=
  match acc with
  | .intro _ _ ih =>
    if h : le (f y) y then y
    else witer le_dec hWiden (hWiden.right y (f y)) (ih hLe h)

/-- Post-fixpoint entry point: `witer` starting from `bot`. -/
def pfp
    {Abstract : Type u}
    {le : Abstract -> Abstract -> Prop}
    {f : Abstract -> Abstract}
    {widen : Widen Abstract}
    (le_dec : ∀ a b : Abstract, Decidable (le a b))
    (hWiden : WidenUpperBound le widen)
    (bot : Abstract)
    (hBot : ∀ a : Abstract, le bot a)
    (acc : WAcc le f widen bot bot) : Abstract :=
  witer le_dec hWiden (hBot bot) acc

end Iteration
end Framework
end AbsInterp
