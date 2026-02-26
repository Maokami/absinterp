import Cslib.Init

import AbsInterpLTS.Framework.Semantics.TraceLift

namespace AbsInterpLTS
namespace Framework

universe u v

/-!
# Concrete Semantic Transformers

This file defines concrete transformers on `Set State` and monotonicity predicates.

Trace lifting is obtained via the generic combinator `liftTrace`.
-/

section Basic

/-- Concrete semantic transformer over concrete state properties. -/
abbrev Post (State : Type u) := Set State -> Set State

/-- Monotonicity predicate for concrete transformers. -/
def MonotonePost {State : Type u} (post : Post State) : Prop :=
  forall {s t : Set State}, s ⊆ t -> post s ⊆ post t

/-- Sequential composition of concrete transformers. -/
def composePost
    {State : Type u}
    (post1 post2 : Post State) :
    Post State :=
  fun states => post2 (post1 states)

end Basic

section Trace

/--
Lift a one-step concrete transformer family to trace transformers.
`liftTracePost stepPost` composes step transformers left-to-right.
-/
def liftTracePost
    {State : Type u}
    {Label : Type v}
    (stepPost : Label -> Post State) :
    List Label -> Post State :=
  liftTrace composePost (fun states => states) stepPost

end Trace

end Framework
end AbsInterpLTS
