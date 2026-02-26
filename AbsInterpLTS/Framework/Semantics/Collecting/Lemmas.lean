import Cslib.Init

import AbsInterpLTS.Framework.Semantics.Collecting.Defs

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
  intro states states' hSubset s hs
  rcases hs with hsInit | hsPost
  · exact Or.inl hsInit
  · exact Or.inr (cfg.monotone hSubset hsPost)

end CollectingStep

end Framework
end AbsInterpLTS
