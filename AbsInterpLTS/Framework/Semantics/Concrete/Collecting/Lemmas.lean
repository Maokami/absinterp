import Cslib.Init
import Mathlib.Data.Set.Basic
import AbsInterpLTS.Framework.Semantics.Concrete.Collecting.Defs

/-!
# Collecting Semantics — Lemmas

Canonical location: `Framework/Semantics/Concrete/Collecting/Lemmas.lean`
-/

namespace AbsInterpLTS
namespace Framework

universe u

namespace CollectingStep

/-!
Lemmas in this namespace operate on concrete collecting transformers
(`Set State -> Set State`), matching the concrete-only contract in
`Collecting/Defs`.
-/

@[simp] theorem reachF_apply
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State)
    (states : Set State) :
    cfg.reachF init states = init ∪ cfg.post states :=
  rfl

theorem reachF_monotone
    {State : Type u}
    (cfg : CollectingStep State)
    (init : Set State) :
    MonotonePost (cfg.reachF init) := by
  intro _ _ hSubset
  exact Set.union_subset_union (Set.Subset.refl _) (cfg.monotone hSubset)

end CollectingStep

end Framework
end AbsInterpLTS
