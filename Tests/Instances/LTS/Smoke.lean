import Cslib.Init

import AbsInterpLTS

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

def oneAbstraction : AbsInterpLTS.Instances.LTS.LTSAbstraction Nat Unit OneAbs where
  lts := emptyNatLTS
  gamma := gammaOne
  transfer := transferOne
  soundStep := by
    intro _ _ s _
    simp [gammaOne]

theorem oneSoundStepExplicit :
    AbsInterpLTS.Framework.SoundStep
      (AbsInterpLTS.Instances.LTS.postStep emptyNatLTS)
      gammaOne
      transferOne := by
  intro _ _ s _
  simp [gammaOne]

example :
    AbsInterpLTS.Framework.MonotonePost
      (AbsInterpLTS.Instances.LTS.postStep oneAbstraction.lts ()) := by
  intro s t hSubset
  exact AbsInterpLTS.Instances.LTS.postStep_monotone oneAbstraction.lts () hSubset

example :
    AbsInterpLTS.Framework.SoundTrace
      (AbsInterpLTS.Framework.liftTracePost
        (AbsInterpLTS.Instances.LTS.postStep oneAbstraction.lts))
      oneAbstraction.gamma
      (AbsInterpLTS.Framework.liftTracePostSharp oneAbstraction.transfer) := by
  exact oneAbstraction.soundTraceLifted

example :
    AbsInterpLTS.Framework.SoundTrace
      (AbsInterpLTS.Framework.liftTracePost
        (AbsInterpLTS.Instances.LTS.postStep emptyNatLTS))
      gammaOne
      (AbsInterpLTS.Framework.liftTracePostSharp transferOne) := by
  exact AbsInterpLTS.Instances.LTS.LTSAbstraction.soundTraceLiftedOfExplicit
      (State := Nat)
      (Label := Unit)
      (Abstract := OneAbs)
      emptyNatLTS
      gammaOne
      transferOne
      oneSoundStepExplicit

end InstancesLTSSmoke
end Tests
