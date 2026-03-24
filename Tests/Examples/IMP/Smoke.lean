import Cslib.Init

import Examples

namespace Tests
namespace ExamplesIMPSmoke

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Instances.LTS
open Examples.IMP
open Examples.IMP.Programs

def assignFive : Stmt :=
  .assign .x0 (.lit 5)

def branchOnX0 : Stmt :=
  .ite (.var .x0) (.assign .x1 (.lit 1)) (.assign .x1 (.lit 0))

def branchInitStore : StoreSharp Sign
  | .x0 => .nonneg
  | .x1 => .top

example :
    (transferProgramSign assignFive .assign (initAt assignFive topStoreSign)) .skip .x0 = .pos := by
  simp [transferProgramSign, assignFive, initAt, singletonConfigSign,
    updateStoreSharp, evalSignExpr, constSign]

example :
    (transferProgramSign branchOnX0 .ifTrue (initAt branchOnX0 branchInitStore))
      (.assign .x1 (.lit 1)) .x0 = .pos := by
  simp [transferProgramSign, branchOnX0, initAt, singletonConfigSign, branchInitStore,
    assumeTrueStore, assumeNonzero, botConfigSign, botStoreSign]

example :
    (transferProgramSign branchOnX0 .ifFalse (initAt branchOnX0 branchInitStore))
      (.assign .x1 (.lit 0)) .x0 = .zero := by
  simp [transferProgramSign, branchOnX0, initAt, singletonConfigSign, branchInitStore,
    assumeFalseStore, assumeZero, botConfigSign, botStoreSign]

example :
    SoundTrace
      (liftTracePost (postStep impLTS))
      (gammaProgramSign branchOnX0)
      (liftTracePostSharp (impSignTransfer branchOnX0)) :=
  (impSignAbstraction branchOnX0).soundTraceLifted

example :
    analyzeShowcase signShowcaseTrueTrace .skip .x0 = .nonneg :=
  analyzeShowcase_trueTrace_skip_x0

example :
    analyzeShowcase signShowcaseFalseTrace [imp| x1 := 0] .x0 = .bot :=
  analyzeShowcase_falseTrace_else_x0

end ExamplesIMPSmoke
end Tests
