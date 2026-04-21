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
  scalarDomain := intervalConcretizationDomain
  bottom := { gamma_bot := rfl }
  const := { point := constInterval, sound := constInterval_sound }
  addTransfer := { transfer := addIntervalTransfer, sound := addIntervalTransfer_sound }
  intersect := { meetLike := meetInterval, sound := meetInterval_sound, reductive := meetInterval_reductive }
  filterNonzero := {
    operator := filterNonzeroInterval
    sound := filterNonzeroInterval_sound
    reductive := filterNonzeroInterval_reductive
  }
  filterZero := {
    operator := filterZeroInterval
    sound := filterZeroInterval_sound
    reductive := filterZeroInterval_reductive
  }

-- Public API wrappers.

/-- Convenient alias for the lifted Interval config domain on IMP configurations. -/
abbrev impConfigIntervalDomain : ConcretizationDomain (ConfigSharp Interval) Config :=
  configConcretizationDomain intervalConcretizationDomain

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

/-! ## Collecting/fixpoint path -/

/-- Unlabeled collecting transfer specialized to the Interval IMP analysis. -/
def impIntervalCollectingTransfer (program : Stmt) :
    PostSharp (ConfigSharp Interval) :=
  impCollectingTransfer intervalAnalysisDomain program

/-- Generic Interval IMP collecting soundness (unlabeled `postAny`). -/
theorem soundAny_impInterval (program : Stmt) :
    Sound (postAny impLTS) (gammaProgramInterval program) (impIntervalCollectingTransfer program) :=
  soundAny_imp intervalAnalysisDomain program

/-- Reach transfer over Interval IMP collecting, for a given abstract initial value. -/
def impIntervalReachTransfer (program : Stmt) (initAbs : ConfigSharp Interval) :
    PostSharp (ConfigSharp Interval) :=
  impReachTransfer intervalAnalysisDomain program initAbs

/-- Interval specialisation of the generic IMP ω-reachable bridge. -/
theorem omegaReachableLTS_subset_of_isPostFixpoint_impInterval
    (program : Stmt) (init : Set Config)
    (initAbs a : ConfigSharp Interval)
    (hInit : init ⊆ gammaProgramInterval program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impIntervalReachTransfer program initAbs) a) :
    omegaReachableLTS impLTS init ⊆ gammaProgramInterval program a :=
  omegaReachableLTS_subset_of_isPostFixpoint_imp intervalAnalysisDomain program init initAbs a hInit hFix

/-- Interval specialisation of the generic IMP Kleene-iterate bridge. -/
theorem kleeneNat_subset_of_isPostFixpoint_impInterval
    (program : Stmt) (init : Set Config)
    (initAbs a : ConfigSharp Interval)
    (hInit : init ⊆ gammaProgramInterval program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impIntervalReachTransfer program initAbs) a) :
    ∀ n, (postAny_collectingStep impLTS).kleeneNat init n ⊆ gammaProgramInterval program a :=
  kleeneNat_subset_of_isPostFixpoint_imp intervalAnalysisDomain program init initAbs a hInit hFix

end Examples.IMP
