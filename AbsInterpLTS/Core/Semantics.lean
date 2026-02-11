import Cslib.Init

namespace AbsInterpLTS
namespace Core

universe u

/-- Concrete semantic transformer over concrete state properties. -/
abbrev Post (State : Type u) := Set State -> Set State

/-- Monotonicity predicate for concrete transformers. -/
def MonotonePost {State : Type u} (post : Post State) : Prop :=
  forall {s t : Set State}, s ⊆ t -> post s ⊆ post t

end Core
end AbsInterpLTS
