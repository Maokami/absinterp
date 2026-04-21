import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Iteration.Fixpoint.Lemmas
import AbsInterp.Framework.Iteration.Collecting
import AbsInterp.Framework.Semantics.Omega.Defs

/-!
# Fixpoint → collecting/omega bridge

Reusable corollaries that turn an abstract post-fixpoint into a sound
over-approximation of collecting Kleene iterates and of ω-reachability.

These are the headline Session 4 results: once a solver has produced an
abstract post-fixpoint, these theorems deliver the concrete safety
conclusion without any further iteration-specific reasoning.
-/

namespace AbsInterp
namespace Framework
namespace Iteration

open AbsInterp.Framework

universe u v

/--
Every finite collecting Kleene iterate is concretized by an abstract
post-fixpoint of the matching reachability transfer.
-/
theorem kleeneNat_subset_of_isPostFixpoint
    {State : Type u} {Abstract : Type v}
    (cfg : CollectingStep State)
    (init : Set State)
    {gamma : Concretization Abstract State}
    {reachSharp : PostSharp Abstract}
    {le : Abstract -> Abstract -> Prop}
    (hSound : Sound (cfg.reachF init) gamma reachSharp)
    (gamma_mono : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b)
    {a : Abstract}
    (hFix : IsPostFixpoint le reachSharp a) :
    ∀ n, cfg.kleeneNat init n ⊆ gamma a := by
  intro n
  have hMono : MonotonePost (cfg.reachF init) := CollectingStep.reachF_monotone cfg init
  have hEmpty : (∅ : Set State) ⊆ gamma a := Set.empty_subset _
  exact sound_iterateNat_from_init_of_isPostFixpoint
    hSound hMono gamma_mono hEmpty hFix n

/--
The union of all finite collecting Kleene iterates is concretized by an
abstract post-fixpoint of the matching reachability transfer.
-/
theorem iUnion_kleeneNat_subset_of_isPostFixpoint
    {State : Type u} {Abstract : Type v}
    (cfg : CollectingStep State)
    (init : Set State)
    {gamma : Concretization Abstract State}
    {reachSharp : PostSharp Abstract}
    {le : Abstract -> Abstract -> Prop}
    (hSound : Sound (cfg.reachF init) gamma reachSharp)
    (gamma_mono : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b)
    {a : Abstract}
    (hFix : IsPostFixpoint le reachSharp a) :
    (⋃ n, cfg.kleeneNat init n) ⊆ gamma a := by
  apply Set.iUnion_subset
  intro n
  exact kleeneNat_subset_of_isPostFixpoint cfg init hSound gamma_mono hFix n

/--
Every ω-reachable state from `init` is concretized by an abstract
post-fixpoint of the matching reachability transfer.

This is the headline bridge: safety properties proved at the abstract
post-fixpoint transfer through to infinite executions of the concrete
collecting semantics.
-/
theorem omegaReachable_subset_of_isPostFixpoint
    {State : Type u} {Abstract : Type v}
    (cfg : CollectingStep State)
    (init : Set State)
    {gamma : Concretization Abstract State}
    {reachSharp : PostSharp Abstract}
    {le : Abstract -> Abstract -> Prop}
    (hSound : Sound (cfg.reachF init) gamma reachSharp)
    (gamma_mono : ∀ {a b : Abstract}, le a b -> gamma a ⊆ gamma b)
    {a : Abstract}
    (hFix : IsPostFixpoint le reachSharp a) :
    omegaReachable cfg init ⊆ gamma a :=
  Set.Subset.trans
    (omegaReachable_subset_iUnion_kleeneNat cfg init)
    (iUnion_kleeneNat_subset_of_isPostFixpoint cfg init hSound gamma_mono hFix)

end Iteration
end Framework
end AbsInterp
