import Cslib.Init

/-!
# Generic post-fixpoint notion

Widening-independent fixpoint vocabulary: `IsPostFixpoint` states that a
function is contracted (or stationary) at a point relative to an order.
Specialized iterative solvers (widening, narrowing, worklist) live in
separate modules and depend on this definition.
-/

namespace AbsInterp
namespace Framework
namespace Iteration

universe u

/-- Post-fixpoint property: `f(a) ⊑ a`. -/
def IsPostFixpoint
    {Abstract : Type u}
    (le : Abstract -> Abstract -> Prop)
    (f : Abstract -> Abstract)
    (a : Abstract) : Prop :=
  le (f a) a

end Iteration
end Framework
end AbsInterp
