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
Unbundled reach transfer, shared by the bundled `LTSCollectingAbstraction`
and by bare-`gamma` clients (e.g. program-relative concretizations that are
not full `ConcretizationDomain`s): add the abstract initial approximation
`initAbs` at every step.
-/
def reachTransferAny
    {Abstract : Type w}
    [SemilatticeSup Abstract]
    (transferAny : PostSharp Abstract)
    (initAbs : Abstract) :
    PostSharp Abstract :=
  fun a => initAbs ⊔ transferAny a

/--
Soundness of `reachTransferAny` against the LTS collecting reachability
operator, stated for a bare concretization `gamma` plus a monotonicity proof.
This is the primary statement; the `ConcretizationDomain`-bundled
`LTSCollectingAbstraction.sound_reachTransfer` is a convenience wrapper and
clients without `gamma_top`/`OrderTop` (such as IMP) call this directly.
-/
theorem sound_reachTransferAny
    {State : Type u}
    {Label : Type v}
    {Abstract : Type w}
    [SemilatticeSup Abstract]
    (lts : Cslib.LTS State Label)
    (gamma : Concretization Abstract State)
    (gamma_mono : ∀ {a b : Abstract}, a ≤ b → gamma a ⊆ gamma b)
    (transferAny : PostSharp Abstract)
    (soundAny : Sound (postAny lts) gamma transferAny)
    {init : Set State}
    {initAbs : Abstract}
    (hInit : init ⊆ gamma initAbs) :
    Sound ((postAny_collectingStep lts).reachF init) gamma
      (reachTransferAny transferAny initAbs) := by
  intro a s hs
  rcases hs with hInitMem | hPostMem
  · have hLeft : initAbs ≤ reachTransferAny transferAny initAbs a := by
      show initAbs ≤ initAbs ⊔ transferAny a
      exact le_sup_left
    exact gamma_mono hLeft (hInit hInitMem)
  · have hRight : transferAny a ≤ reachTransferAny transferAny initAbs a := by
      show transferAny a ≤ initAbs ⊔ transferAny a
      exact le_sup_right
    exact gamma_mono hRight (soundAny a hPostMem)

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
  reachTransferAny cfg.transferAny initAbs

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
      (cfg.reachTransfer initAbs) :=
  sound_reachTransferAny cfg.lts cfg.domain.gamma
    (fun h => cfg.domain.gamma_monotone h) cfg.transferAny cfg.soundAny hInit

end LTSCollectingAbstraction

end LTS
end Instances
end AbsInterp
