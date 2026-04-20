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
# Sign Analysis — Domain Instance

Thin wrapper that instantiates the generic IMP analysis for the Sign domain.
All transfer functions and soundness proofs are inherited from `Generic/`.
-/

/-- IMP analysis domain instance for Sign. -/
def signAnalysisDomain : IMPAnalysisDomain Sign where
  scalarDomain := signConcretizationDomain
  gamma_bot := rfl
  const := constSign
  const_sound := constSign_sound
  addTransfer := addTransfer
  addTransfer_sound := addTransfer_sound
  intersect := meetSign
  intersect_sound := meetSign_sound
  intersect_reductive := meetSign_reductive
  filterNonzero := filterNonzeroSign
  filterNonzero_sound := filterNonzeroSign_sound
  filterNonzero_reductive := filterNonzeroSign_reductive
  filterZero := filterZeroSign
  filterZero_sound := filterZeroSign_sound
  filterZero_reductive := filterZeroSign_reductive
  backwardAddNonzero := backwardAddNonzeroSign
  backwardAddNonzero_sound := backwardAddNonzeroSign_sound
  backwardAddNonzero_reductive := backwardAddNonzeroSign_reductive
  backwardAddZero := backwardAddZeroSign
  backwardAddZero_sound := backwardAddZeroSign_sound
  backwardAddZero_reductive := backwardAddZeroSign_reductive

-- Public API wrappers.

/-- Convenient alias for the lifted Sign config domain on IMP configurations. -/
abbrev impConfigSignDomain : ConcretizationDomain (ConfigSharp Sign) Config :=
  configConcretizationDomain signConcretizationDomain

/-- The generic Sign concretization for a fixed IMP program. -/
def gammaProgramSign (program : Stmt) : Framework.Concretization (ConfigSharp Sign) Config :=
  gammaProgram signAnalysisDomain program

/-- Top abstract store for IMP Sign analysis. -/
def topStoreSign : StoreSharp Sign := fun _ => .top

/-- Abstract expression evaluation over Sign stores. -/
def evalSignExpr := evalExpr signAnalysisDomain

/-- Generic Sign transfer for the labeled IMP LTS. -/
def transferProgramSign := transferProgram signAnalysisDomain

/-- Package the generic Sign transfer as a framework step transformer. -/
def impSignTransfer (program : Stmt) : StepPostSharp (ConfigSharp Sign) StepLabel :=
  impTransfer signAnalysisDomain program

/-- One-step soundness of the generic Sign transfer over the canonical labeled IMP LTS. -/
theorem soundStep_impSign (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgramSign program) (impSignTransfer program) :=
  soundStep_imp signAnalysisDomain program

/-- LTS abstraction packaging the generic Sign IMP analysis for a fixed program. -/
def impSignAbstraction (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp Sign) :=
  impAbstraction signAnalysisDomain program

end Examples.IMP
