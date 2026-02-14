import Cslib.Init
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

import AbsInterpLTS.Framework.Semantics.TraceLift

namespace AbsInterpLTS
namespace Framework

universe u v

/-!
# Concrete Semantic Transformers

This file defines concrete transformers on `Set State`, monotonicity predicates,
and `OrderHom` encodings.

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

section Hom

/-- Order-hom encoding of concrete semantic transformers. -/
abbrev PostHom (State : Type u) := OrderHom (Set State) (Set State)

/-- Build an order-hom from a monotone concrete transformer. -/
def Post.toHom
    {State : Type u}
    (post : Post State)
    (hMono : MonotonePost post) :
    PostHom State where
  toFun := post
  monotone' := by
    intro s t hSubset
    exact hMono hSubset

/-- Forget the order-hom structure and view it as a plain transformer. -/
def PostHom.toPost
    {State : Type u}
    (post : PostHom State) :
    Post State :=
  post.toFun

/-- Composition of order-hom transformers. -/
def composePostHom
    {State : Type u}
    (post1 post2 : PostHom State) :
    PostHom State :=
  OrderHom.comp post2 post1

/-- Label-indexed concrete transformers represented as order homomorphisms. -/
abbrev StepPostHom (State : Type u) (Label : Type v) := Label -> PostHom State

/-- Trace-indexed concrete transformers represented as order homomorphisms. -/
abbrev TracePostHom (State : Type u) (Label : Type v) := List Label -> PostHom State

end Hom

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

/--
Lift a one-step order-hom family to trace transformers by composition.
-/
def liftTracePostHom
    {State : Type u}
    {Label : Type v}
    (stepPost : StepPostHom State Label) :
    TracePostHom State Label :=
  liftTrace composePostHom OrderHom.id stepPost

end Trace

end Framework
end AbsInterpLTS
