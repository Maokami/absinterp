import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Iteration.Fixpoint
import AbsInterp.Instances.LTS.Semantics.Omega
import AbsInterp.Instances.LTS.Instantiation.CollectingInterface

/-!
# LTS collecting/fixpoint bridge theorems

Reusable corollaries that combine:

- the LTS unlabeled collecting semantics (`postAny_collectingStep`),
- a sound abstract collecting transfer bundled as `LTSCollectingAbstraction`,
- the generic post-fixpoint bridge.

Each theorem takes an abstract post-fixpoint of `cfg.reachTransfer initAbs`
and concludes a concrete safety statement: every finite Kleene iterate,
the full union of Kleene iterates, or every LTS ω-reachable state is
contained in the concretization of that post-fixpoint.
-/

namespace AbsInterp
namespace Instances
namespace LTS

open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Framework.Iteration

namespace LTSCollectingAbstraction

universe u v w

variable
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    [SemilatticeSup Abstract]
    [OrderTop Abstract]

/--
If `init ⊆ γ(initAbs)` and `a` is a post-fixpoint of `cfg.reachTransfer initAbs`,
then every finite Kleene iterate of the LTS collecting semantics from `init`
is concretized by `a`.
-/
theorem kleeneNat_subset_of_isPostFixpoint
    (cfg : LTSCollectingAbstraction State Label Abstract)
    (init : Set State)
    (initAbs a : Abstract)
    (hInit : init ⊆ cfg.domain.gamma initAbs)
    (hFix : IsPostFixpoint (· ≤ ·) (cfg.reachTransfer initAbs) a) :
    ∀ n, (postAny_collectingStep cfg.lts).kleeneNat init n ⊆ cfg.domain.gamma a :=
  Iteration.kleeneNat_subset_of_isPostFixpoint
    (postAny_collectingStep cfg.lts) init
    (cfg.sound_reachTransfer hInit)
    (fun h => cfg.domain.gamma_monotone h)
    hFix

/--
Under the same hypotheses, the union of all finite Kleene iterates is
concretized by `a`.
-/
theorem iUnion_kleeneNat_subset_of_isPostFixpoint
    (cfg : LTSCollectingAbstraction State Label Abstract)
    (init : Set State)
    (initAbs a : Abstract)
    (hInit : init ⊆ cfg.domain.gamma initAbs)
    (hFix : IsPostFixpoint (· ≤ ·) (cfg.reachTransfer initAbs) a) :
    (⋃ n, (postAny_collectingStep cfg.lts).kleeneNat init n) ⊆ cfg.domain.gamma a :=
  Iteration.iUnion_kleeneNat_subset_of_isPostFixpoint
    (postAny_collectingStep cfg.lts) init
    (cfg.sound_reachTransfer hInit)
    (fun h => cfg.domain.gamma_monotone h)
    hFix

/--
Headline bridge: every state on a CSLib `ωTr` of `cfg.lts` starting in
`init` is concretized by an abstract post-fixpoint of
`cfg.reachTransfer initAbs`.

This composes `omegaReachableLTS_subset_omegaReachable` with the generic
`omegaReachable_subset_of_isPostFixpoint`.
-/
theorem omegaReachableLTS_subset_of_isPostFixpoint
    (cfg : LTSCollectingAbstraction State Label Abstract)
    (init : Set State)
    (initAbs a : Abstract)
    (hInit : init ⊆ cfg.domain.gamma initAbs)
    (hFix : IsPostFixpoint (· ≤ ·) (cfg.reachTransfer initAbs) a) :
    omegaReachableLTS cfg.lts init ⊆ cfg.domain.gamma a :=
  Set.Subset.trans
    (omegaReachableLTS_subset_omegaReachable cfg.lts init)
    (Iteration.omegaReachable_subset_of_isPostFixpoint
      (postAny_collectingStep cfg.lts) init
      (cfg.sound_reachTransfer hInit)
      (fun h => cfg.domain.gamma_monotone h)
      hFix)

end LTSCollectingAbstraction

end LTS
end Instances
end AbsInterp
