import Cslib.Init

import Examples

namespace Tests
namespace ExamplesIMPSmoke

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Instances.LTS
open Examples.IMP
open Examples.IMP.Programs

def assignFive : Stmt :=
  .assign Var.x0 (.lit 5)

def branchOnX0 : Stmt :=
  .ite (.var Var.x0) (.assign Var.x1 (.lit 1)) (.assign Var.x1 (.lit 0))

def branchInitStore : StoreSharp Sign := fun x =>
  if x = Var.x0 then .nonneg else .top

example :
    (transferProgramSign assignFive .assign (initAt assignFive topStoreSign)) .skip Var.x0 = .pos := by
  native_decide

example :
    (transferProgramSign branchOnX0 .ifTrue (initAt branchOnX0 branchInitStore))
      (.assign Var.x1 (.lit 1)) Var.x0 = .pos := by
  native_decide

example :
    (transferProgramSign branchOnX0 .ifFalse (initAt branchOnX0 branchInitStore))
      (.assign Var.x1 (.lit 0)) Var.x0 = .zero := by
  native_decide

example :
    SoundTrace
      (liftTracePost (postStep impLTS))
      (gammaProgramSign branchOnX0)
      (liftTracePostSharp (impSignTransfer branchOnX0)) :=
  (impSignAbstraction branchOnX0).soundTraceLifted

example :
    analyzeShowcase signShowcaseTrueTrace .skip Var.x0 = .nonneg :=
  analyzeShowcase_trueTrace_skip_x0

example :
    analyzeShowcase signShowcaseFalseTrace [imp| x1 := 0] Var.x0 = .bot :=
  analyzeShowcase_falseTrace_else_x0

end ExamplesIMPSmoke
end Tests
