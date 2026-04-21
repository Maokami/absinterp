import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import AbsInterp.Framework.Domains.Concretization
import AbsInterp.Framework.Soundness.Defs
import AbsInterp.Instances.LTS.Semantics.Collecting

/-!
# LTS Collecting Abstraction Interface

`LTSCollectingAbstraction` packages a CSLib LTS with an **unlabeled**
collecting transfer function that is sound w.r.t. `postAny`. It is
intentionally parallel to (and independent from) `LTSAbstraction`, which
captures the labeled one-step soundness obligation used for trace
soundness.

This interface is the adapter from the LTS collecting semantics to the
generic Session 4 post-fixpoint bridge
(`AbsInterp.Framework.Iteration.Fixpoint.Collecting`).
-/

namespace AbsInterp
namespace Instances
namespace LTS

open AbsInterp.Framework
open AbsInterp.Framework.Domains

universe u v w

/--
Reusable interface for unlabeled collecting abstract interpretation over a
CSLib LTS.

Fields:
- `lts`: the underlying CSLib LTS.
- `domain`: a γ-only concretization domain on `Abstract`.
- `transferAny`: abstract transfer for the unlabeled `postAny` semantics.
- `soundAny`: one-step soundness of `transferAny` w.r.t. `postAny lts`.

Why a separate structure from `LTSAbstraction`:
- `LTSAbstraction` takes a **labeled** transfer (`Label → Abstract → Abstract`)
  and targets trace soundness.
- `LTSCollectingAbstraction` takes an **unlabeled** transfer (`Abstract →
  Abstract`) and targets collecting/fixpoint reasoning. Deriving the latter
  from the former requires extra assumptions (e.g. finite label
  enumeration, abstract join aggregation) that this layer deliberately
  avoids.
-/
structure LTSCollectingAbstraction
    (State : Type u)
    (Label : Type v)
    (Abstract : Type w)
    [SemilatticeSup Abstract]
    [OrderTop Abstract] where
  /-- The underlying CSLib LTS. -/
  lts : Cslib.LTS State Label
  /-- A γ-only concretization domain over `Abstract`. -/
  domain : ConcretizationDomain Abstract State
  /-- Abstract transfer for the unlabeled `postAny` semantics. -/
  transferAny : PostSharp Abstract
  /-- One-step soundness of `transferAny` w.r.t. the LTS collecting step. -/
  soundAny : Sound (postAny lts) domain.gamma transferAny

namespace LTSCollectingAbstraction

variable
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    [SemilatticeSup Abstract]
    [OrderTop Abstract]

/--
Reachability transformer lifting an abstract entry approximation `initAbs`:

`reachTransfer cfg initAbs a = initAbs ⊔ cfg.transferAny a`.

This matches `(postAny_collectingStep cfg.lts).reachF init` once `init`
is over-approximated by `initAbs`, and is the abstract object we iterate
with a widening solver to reach a post-fixpoint.
-/
def reachTransfer
    (cfg : LTSCollectingAbstraction State Label Abstract)
    (initAbs : Abstract) :
    PostSharp Abstract :=
  fun a => initAbs ⊔ cfg.transferAny a

/--
The abstract reachability transfer is sound w.r.t. the concrete LTS
collecting reachability operator whenever the initial concrete set is
bounded by `initAbs`.
-/
theorem sound_reachTransfer
    (cfg : LTSCollectingAbstraction State Label Abstract)
    {init : Set State}
    {initAbs : Abstract}
    (hInit : init ⊆ cfg.domain.gamma initAbs) :
    Sound ((postAny_collectingStep cfg.lts).reachF init)
      cfg.domain.gamma
      (cfg.reachTransfer initAbs) := by
  intro a s hs
  rcases hs with hInitMem | hPostMem
  ·
    have hLeft : initAbs ≤ cfg.reachTransfer initAbs a := by
      change initAbs ≤ initAbs ⊔ cfg.transferAny a
      exact le_sup_left
    exact cfg.domain.gamma_monotone hLeft (hInit hInitMem)
  ·
    have hRight : cfg.transferAny a ≤ cfg.reachTransfer initAbs a := by
      change cfg.transferAny a ≤ initAbs ⊔ cfg.transferAny a
      exact le_sup_right
    exact cfg.domain.gamma_monotone hRight (cfg.soundAny a hPostMem)

end LTSCollectingAbstraction

end LTS
end Instances
end AbsInterp
