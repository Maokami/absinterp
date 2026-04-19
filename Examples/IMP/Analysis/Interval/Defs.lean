import AbsInterp.Domains
import AbsInterp.Framework
import AbsInterp.Instances.LTS
import Examples.IMP.Analysis.Generic

namespace Examples.IMP

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Instances.LTS

/-!
# Interval Analysis — Domain Instance

Thin wrapper that instantiates the generic IMP analysis for the Interval domain.
All transfer functions and soundness proofs are inherited from `Generic/`.
-/

/-- IMP analysis domain instance for Interval. -/
def intervalAnalysisDomain : IMPAnalysisDomain Interval where
  scalarDomain := intervalGammaDomain
  gamma_bot := rfl
  const := constInterval
  const_sound := constInterval_sound
  addTransfer := addIntervalTransfer
  addTransfer_sound := addIntervalTransfer_sound
  filterNonzero := filterNonzeroInterval
  filterNonzero_sound := filterNonzeroInterval_sound
  filterNonzero_reductive := filterNonzeroInterval_reductive
  filterZero := filterZeroInterval
  filterZero_sound := filterZeroInterval_sound
  filterZero_reductive := filterZeroInterval_reductive
  backwardAddNonzero_sound :=
    SoundBackwardOperator.id (gamma := intervalGammaDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ ≠ 0)
  backwardAddNonzero_reductive := ReductiveBackwardOperator.id
  backwardAddZero_sound :=
    SoundBackwardOperator.id (gamma := intervalGammaDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ = 0)
  backwardAddZero_reductive := ReductiveBackwardOperator.id

-- Public API wrappers.

/-- Convenient alias for the lifted Interval config domain on IMP configurations. -/
abbrev impConfigIntervalDomain : GammaDomain (ConfigSharp Interval) Config :=
  configGammaDomain intervalGammaDomain

/-- The generic Interval concretization for a fixed IMP program. -/
def gammaProgramInterval (program : Stmt) : Framework.Concretization (ConfigSharp Interval) Config :=
  gammaProgram intervalAnalysisDomain program

/-- Top abstract store for IMP Interval analysis. -/
def topStoreInterval : StoreSharp Interval := fun _ => .top

/-- Abstract expression evaluation over Interval stores. -/
def evalIntervalExpr := evalExpr intervalAnalysisDomain

/-- Generic Interval transfer for the labeled IMP LTS. -/
def transferProgramInterval := transferProgram intervalAnalysisDomain

/-- Package the generic Interval transfer as a framework step transformer. -/
def impIntervalTransfer (program : Stmt) : StepPostSharp (ConfigSharp Interval) StepLabel :=
  impTransfer intervalAnalysisDomain program

/-- One-step soundness of the generic Interval transfer over the canonical labeled IMP LTS. -/
theorem soundStep_impInterval (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgramInterval program) (impIntervalTransfer program) :=
  soundStep_imp intervalAnalysisDomain program

/-- LTS abstraction packaging the generic Interval IMP analysis for a fixed program. -/
def impIntervalAbstraction (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp Interval) :=
  impAbstraction intervalAnalysisDomain program

end Examples.IMP
