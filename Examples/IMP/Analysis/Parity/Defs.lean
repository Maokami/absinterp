import AbsInterp.Domains.Parity
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
# Parity Analysis — Domain Instance

Thin wrapper that instantiates the generic IMP analysis for the Parity domain.
Validates that adding a new domain to the generic framework requires minimal code.
-/

/-- IMP analysis domain instance for Parity. -/
def parityAnalysisDomain : IMPAnalysisDomain Parity where
  scalarDomain := parityGammaDomain
  gamma_bot := rfl
  const := constParity
  const_sound := constParity_sound
  addTransfer := addParityTransfer
  addTransfer_sound := addParityTransfer_sound
  filterNonzero := filterNonzeroParity
  filterNonzero_sound := filterNonzeroParity_sound
  filterNonzero_reductive := filterNonzeroParity_reductive
  filterZero := filterZeroParity
  filterZero_sound := filterZeroParity_sound
  filterZero_reductive := filterZeroParity_reductive
  backwardAddNonzero_sound :=
    SoundBackwardOperator.id (gamma := parityGammaDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ ≠ 0)
  backwardAddNonzero_reductive := ReductiveBackwardOperator.id
  backwardAddZero_sound :=
    SoundBackwardOperator.id (gamma := parityGammaDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ = 0)
  backwardAddZero_reductive := ReductiveBackwardOperator.id

/-- The generic Parity concretization for a fixed IMP program. -/
def gammaProgramParity (program : Stmt) : Framework.Concretization (ConfigSharp Parity) Config :=
  gammaProgram parityAnalysisDomain program

/-- Top abstract store for IMP Parity analysis. -/
def topStoreParity : StoreSharp Parity := fun _ => .top

/-- Generic Parity transfer for the labeled IMP LTS. -/
def transferProgramParity := transferProgram parityAnalysisDomain

/-- Package the generic Parity transfer as a framework step transformer. -/
def impParityTransfer (program : Stmt) : StepPostSharp (ConfigSharp Parity) StepLabel :=
  impTransfer parityAnalysisDomain program

/-- One-step soundness of the generic Parity transfer over the canonical labeled IMP LTS. -/
theorem soundStep_impParity (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgramParity program) (impParityTransfer program) :=
  soundStep_imp parityAnalysisDomain program

/-- LTS abstraction packaging the generic Parity IMP analysis for a fixed program. -/
def impParityAbstraction (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp Parity) :=
  impAbstraction parityAnalysisDomain program

end Examples.IMP
