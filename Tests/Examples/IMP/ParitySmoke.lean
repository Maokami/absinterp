import Cslib.Init

import Examples

namespace Tests
namespace ExamplesIMPParitySmoke

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Instances.LTS
open Examples.IMP

/-!
# Parity Analysis Smoke Tests

Validates the Parity domain instantiation of the generic IMP analysis framework.
-/

/-- `x0 := 5` assigns an odd value. -/
def assignOdd : Stmt :=
  .assign Var.x0 (.lit 5)

/-- `x0 := 4` assigns an even value. -/
def assignEven : Stmt :=
  .assign Var.x0 (.lit 4)

/-- `x0 := 5; x1 := x0 + x0` — odd + odd = even. -/
def addOddOdd : Stmt :=
  .seq (.assign Var.x0 (.lit 5)) (.assign Var.x1 (.add (.var Var.x0) (.var Var.x0)))

example :
    (transferProgramParity assignOdd .assign (initAt assignOdd topStoreParity))
      .skip Var.x0 = .odd := by
  native_decide

example :
    (transferProgramParity assignEven .assign (initAt assignEven topStoreParity))
      .skip Var.x0 = .even := by
  native_decide

/-- odd + odd = even, validated along a two-step trace. -/
example :
    (liftTracePostSharp (impParityTransfer addOddOdd)
      [.seqStep .assign, .seqDone, .assign]
      (initAt addOddOdd topStoreParity))
      .skip Var.x1 = .even := by
  native_decide

/-- Soundness: the Parity analysis is trace-sound over the canonical IMP LTS. -/
example :
    SoundTrace
      (liftTracePost (postStep impLTS))
      (gammaProgramParity assignOdd)
      (liftTracePostSharp (impParityTransfer assignOdd)) :=
  (impParityAbstraction assignOdd).soundTraceLifted

end ExamplesIMPParitySmoke
end Tests
