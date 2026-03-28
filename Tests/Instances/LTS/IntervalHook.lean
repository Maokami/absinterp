import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSIntervalHook

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Instances.LTS
open AbsInterp.Instances.LTS.Analyses

def toyLTS : Cslib.LTS Int Bool where
  Tr s label s' := (label = false ∧ s' = s) ∨ (label = true ∧ s' = 0)

def readId : Int -> Int := fun s => s

def transferToy : Bool -> Interval -> Interval
  | false, a => a
  | true, _ => mk 0 0

theorem stepSoundToy :
    IntervalStepSound toyLTS readId transferToy := by
  intro label a s s' hs htr
  rcases htr with hKeep | hZero
  · rcases hKeep with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simpa [gammaIntervalState, readId, transferToy] using hs
  · rcases hZero with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simp [readId, transferToy, gammaInterval, mk]

example :
    SoundStep (postStep toyLTS) (gammaIntervalState readId) transferToy := by
  exact soundStep_postStep_interval_of_stepSound toyLTS readId transferToy stepSoundToy

def toyIntervalAbstraction : LTSAbstraction Int Bool Interval :=
  intervalAbstractionOfStepSound toyLTS readId transferToy stepSoundToy

example :
    SoundTrace
      (liftTracePost (postStep toyLTS))
      (gammaIntervalState readId)
      (liftTracePostSharp transferToy) := by
  exact toyIntervalAbstraction.soundTraceLifted

end InstancesLTSIntervalHook
end Tests
