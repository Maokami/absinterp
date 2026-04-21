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
  scalarDomain := parityConcretizationDomain
  bottom := { gamma_bot := rfl }
  const := { point := constParity, sound := constParity_sound }
  addTransfer := { transfer := addParityTransfer, sound := addParityTransfer_sound }
  intersect := { meetLike := intersectParity, sound := intersectParity_sound, reductive := intersectParity_reductive }
  filterNonzero := {
    operator := filterNonzeroParity
    sound := filterNonzeroParity_sound
    reductive := filterNonzeroParity_reductive
  }
  filterZero := {
    operator := filterZeroParity
    sound := filterZeroParity_sound
    reductive := filterZeroParity_reductive
  }

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

/-! ## Collecting/fixpoint path -/

/-- Unlabeled collecting transfer specialized to the Parity IMP analysis. -/
def impParityCollectingTransfer (program : Stmt) :
    PostSharp (ConfigSharp Parity) :=
  impCollectingTransfer parityAnalysisDomain program

/-- Generic Parity IMP collecting soundness (unlabeled `postAny`). -/
theorem soundAny_impParity (program : Stmt) :
    Sound (postAny impLTS) (gammaProgramParity program) (impParityCollectingTransfer program) :=
  soundAny_imp parityAnalysisDomain program

/-- Reach transfer over Parity IMP collecting, for a given abstract initial value. -/
def impParityReachTransfer (program : Stmt) (initAbs : ConfigSharp Parity) :
    PostSharp (ConfigSharp Parity) :=
  impReachTransfer parityAnalysisDomain program initAbs

/-- Parity specialisation of the generic IMP ω-reachable bridge. -/
theorem omegaReachableLTS_subset_of_isPostFixpoint_impParity
    (program : Stmt) (init : Set Config)
    (initAbs a : ConfigSharp Parity)
    (hInit : init ⊆ gammaProgramParity program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impParityReachTransfer program initAbs) a) :
    omegaReachableLTS impLTS init ⊆ gammaProgramParity program a :=
  omegaReachableLTS_subset_of_isPostFixpoint_imp parityAnalysisDomain program init initAbs a hInit hFix

/-- Parity specialisation of the generic IMP Kleene-iterate bridge. -/
theorem kleeneNat_subset_of_isPostFixpoint_impParity
    (program : Stmt) (init : Set Config)
    (initAbs a : ConfigSharp Parity)
    (hInit : init ⊆ gammaProgramParity program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impParityReachTransfer program initAbs) a) :
    ∀ n, (postAny_collectingStep impLTS).kleeneNat init n ⊆ gammaProgramParity program a :=
  kleeneNat_subset_of_isPostFixpoint_imp parityAnalysisDomain program init initAbs a hInit hFix

end Examples.IMP
