import Cslib.Init

import AbsInterp.Framework.Iteration.Fixpoint.Defs
import AbsInterp.Framework.Iteration.NatIter
import AbsInterp.Framework.Soundness.Defs

/-!
# Generic post-fixpoint soundness lemmas

Widening-independent soundness consequences of a post-fixpoint. These
lemmas are reusable by any fixpoint-producing solver (widening, narrowing,
Kleene, worklist) and by collecting/omega-level bridges.
-/

namespace AbsInterp
namespace Framework
namespace Iteration

open AbsInterp.Framework

universe u v

/--
Gamma soundness from a post-fixpoint.

If `postSharp` has a post-fixpoint `a` and `Sound` holds, then every
natural-number concrete iterate starting from `gamma a` stays in `gamma a`.
-/
theorem sound_of_isPostFixpoint
    {State : Type u} {Abstract : Type v}
    {post : Post State}
    {gamma : Concretization Abstract State}
    {postSharp : PostSharp Abstract}
    {le : Abstract -> Abstract -> Prop}
    (hSound : Sound post gamma postSharp)
    (hMono : MonotonePost post)
    (gamma_mono : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b)
    {a : Abstract}
    (hFix : IsPostFixpoint le postSharp a) :
    ∀ n, iterateNat post (gamma a) n ⊆ gamma a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterateNat_succ]
    calc post (iterateNat post (gamma a) n)
        ⊆ post (gamma a) := hMono ih
      _ ⊆ gamma (postSharp a) := hSound a
      _ ⊆ gamma a := gamma_mono hFix

/--
Generic bridge from arbitrary initial concrete sets to post-fixpoint soundness.

If `init ⊆ gamma a` and `a` is a post-fixpoint of a sound abstract transfer,
then every natural-number iterate from `init` is soundly abstracted by `a`.
-/
theorem sound_iterateNat_from_init_of_isPostFixpoint
    {State : Type u} {Abstract : Type v}
    {post : Post State}
    {gamma : Concretization Abstract State}
    {postSharp : PostSharp Abstract}
    {le : Abstract -> Abstract -> Prop}
    (hSound : Sound post gamma postSharp)
    (hMono : MonotonePost post)
    (gamma_mono : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b)
    {init : Set State}
    {a : Abstract}
    (hInit : init ⊆ gamma a)
    (hFix : IsPostFixpoint le postSharp a) :
    ∀ n, iterateNat post init n ⊆ gamma a := by
  intro n
  have hChain : iterateNat post init n ⊆ iterateNat post (gamma a) n :=
    iterateNat_monotone_init hMono n hInit
  exact Set.Subset.trans hChain
    (sound_of_isPostFixpoint hSound hMono gamma_mono hFix n)

end Iteration
end Framework
end AbsInterp
