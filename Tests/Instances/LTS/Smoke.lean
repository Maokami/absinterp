import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSSmoke

inductive OneAbs where
  | top
  deriving DecidableEq, Repr

def emptyNatLTS : Cslib.LTS Nat Unit where
  Tr _ _ _ := False

def gammaOne : OneAbs -> Set Nat
  | .top => Set.univ

def transferOne : Unit -> OneAbs -> OneAbs :=
  fun _ a => a

def oneAbstraction : AbsInterp.Instances.LTS.LTSAbstraction Nat Unit OneAbs where
  lts := emptyNatLTS
  gamma := gammaOne
  transfer := transferOne
  soundStep := by
    intro _ _ s _
    simp [gammaOne]

theorem oneSoundStepExplicit :
    AbsInterp.Framework.SoundStep
      (AbsInterp.Instances.LTS.postStep emptyNatLTS)
      gammaOne
      transferOne := by
  intro _ _ s _
  simp [gammaOne]

example :
    AbsInterp.Framework.MonotonePost
      (AbsInterp.Instances.LTS.postStep oneAbstraction.lts ()) := by
  intro s t hSubset
  exact AbsInterp.Instances.LTS.postStep_monotone oneAbstraction.lts () hSubset

example :
    AbsInterp.Instances.LTS.postTrace emptyNatLTS =
      AbsInterp.Framework.liftTracePost (AbsInterp.Instances.LTS.postStep emptyNatLTS) := by
  exact AbsInterp.Instances.LTS.postTrace_eq_liftTracePost_postStep emptyNatLTS

example :
    AbsInterp.Framework.MonotonePost
      (AbsInterp.Instances.LTS.postTrace emptyNatLTS [()]) := by
  exact AbsInterp.Instances.LTS.postTrace_monotone emptyNatLTS [()]

example :
    AbsInterp.Framework.SoundTrace
      (AbsInterp.Framework.liftTracePost
        (AbsInterp.Instances.LTS.postStep oneAbstraction.lts))
      oneAbstraction.gamma
      (AbsInterp.Framework.liftTracePostSharp oneAbstraction.transfer) := by
  exact oneAbstraction.soundTraceLifted

example :
    AbsInterp.Framework.SoundTrace
      (AbsInterp.Framework.liftTracePost
        (AbsInterp.Instances.LTS.postStep emptyNatLTS))
      gammaOne
      (AbsInterp.Framework.liftTracePostSharp transferOne) := by
  exact AbsInterp.Instances.LTS.LTSAbstraction.soundTraceLiftedOfExplicit
      (State := Nat)
      (Label := Unit)
      (Abstract := OneAbs)
      emptyNatLTS
      gammaOne
      transferOne
      oneSoundStepExplicit

end InstancesLTSSmoke
end Tests
