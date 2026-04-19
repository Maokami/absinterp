import Cslib.Init

import AbsInterp.Framework.Semantics.Concrete.Defs
import AbsInterp.Framework.Soundness.Defs

namespace AbsInterp
namespace Framework

universe u v w

/-!
# Weak Semantics Interfaces

Generic closure-based weak semantics.  A closure operator models the
effect of silent (τ) transitions at the framework level, without
depending on any particular LTS library.

The headline result shape is: strong soundness + gamma-closure
implies weak soundness.
-/

section ClosureOp

/-- A closure operator on sets of states. -/
structure ClosureOp (State : Type u) where
  /-- The closure map. -/
  cl : Set State → Set State
  /-- Closure is extensive: `S ⊆ cl S`. -/
  extensive : ∀ S, S ⊆ cl S
  /-- Closure is monotone. -/
  monotone : ∀ {S T : Set State}, S ⊆ T → cl S ⊆ cl T
  /-- Closure is idempotent: `cl (cl S) = cl S`. -/
  idempotent : ∀ S, cl (cl S) = cl S

/-- Weak post: `cl ∘ post ∘ cl`. -/
def weakPost
    {State : Type u}
    (cl : ClosureOp State)
    (post : Post State) :
    Post State :=
  fun states => cl.cl (post (cl.cl states))

/-- Monotonicity of weak post from monotonicity of the underlying post. -/
theorem weakPost_monotone
    {State : Type u}
    {cl : ClosureOp State}
    {post : Post State}
    (hMono : MonotonePost post) :
    MonotonePost (weakPost cl post) := by
  intro S T hSub
  exact cl.monotone (hMono (cl.monotone hSub))

end ClosureOp

section Soundness

/--
A concretization is closed under a closure operator when
`cl (gamma a) ⊆ gamma a` for every abstract element.
-/
def GammaClosed
    {State : Type u}
    {Abstract : Type v}
    (cl : ClosureOp State)
    (gamma : Concretization Abstract State) : Prop :=
  ∀ a, cl.cl (gamma a) ⊆ gamma a

/--
**Key theorem**: strong soundness + gamma-closure implies weak soundness.

If `post (gamma a) ⊆ gamma (postSharp a)` and `cl (gamma a) ⊆ gamma a`,
then `(cl ∘ post ∘ cl) (gamma a) ⊆ gamma (postSharp a)`.
-/
theorem sound_weak_of_sound_closure
    {State : Type u}
    {Abstract : Type v}
    {post : Post State}
    {gamma : Concretization Abstract State}
    {postSharp : PostSharp Abstract}
    {cl : ClosureOp State}
    (hSound : Sound post gamma postSharp)
    (hMono : MonotonePost post)
    (hClosed : GammaClosed cl gamma) :
    Sound (weakPost cl post) gamma postSharp := by
  intro a s hs
  simp only [weakPost] at hs
  have hClGamma : cl.cl (gamma a) ⊆ gamma a := hClosed a
  have hPostCl : post (cl.cl (gamma a)) ⊆ post (gamma a) := hMono hClGamma
  have hPostSound : post (gamma a) ⊆ gamma (postSharp a) := hSound a
  have hInner : post (cl.cl (gamma a)) ⊆ gamma (postSharp a) :=
    fun _ h => hPostSound (hPostCl h)
  have hOuter : cl.cl (post (cl.cl (gamma a))) ⊆ cl.cl (gamma (postSharp a)) :=
    cl.monotone hInner
  exact hClosed (postSharp a) (hOuter hs)

/--
Label-indexed variant: step-wise strong soundness + gamma-closure
implies step-wise weak soundness.
-/
theorem soundStep_weak_of_soundStep_closure
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    {stepPost : StepPost State Label}
    {gamma : Concretization Abstract State}
    {stepPostSharp : StepPostSharp Abstract Label}
    {cl : ClosureOp State}
    (hSound : SoundStep stepPost gamma stepPostSharp)
    (hStepMono : ∀ label, MonotonePost (stepPost label))
    (hClosed : GammaClosed cl gamma) :
    SoundStep (fun label => weakPost cl (stepPost label)) gamma stepPostSharp := by
  intro label a
  exact sound_weak_of_sound_closure (hSound label) (hStepMono label) hClosed a

end Soundness

end Framework
end AbsInterp
