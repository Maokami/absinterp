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
  scalarDomain := parityGammaOnlyDomain
  gamma_bot := rfl
  const := constParity
  const_sound := constParity_sound
  addTransfer := addParityTransfer
  addTransfer_sound := addParityTransfer_sound
  assumeNonzero := assumeNonzeroParity
  assumeNonzero_sound := assumeNonzeroParity_sound
  assumeZero := assumeZeroParity
  assumeZero_sound := assumeZeroParity_sound
  assumeNonzeroAdd_sound :=
    SoundBackwardRefine.id (gamma := parityGammaOnlyDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ ≠ 0)
  assumeZeroAdd_sound :=
    SoundBackwardRefine.id (gamma := parityGammaOnlyDomain.gamma)
      (rel := fun v₁ v₂ => v₁ + v₂ = 0)

/-- The generic Parity concretization for a fixed IMP program. -/
def gammaProgramParity (program : Stmt) : Framework.Gamma (ConfigSharp Parity) Config :=
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
