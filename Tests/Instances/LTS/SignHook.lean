import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSSignHook

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Instances.LTS
open AbsInterp.Instances.LTS.Analyses

def toyLTS : Cslib.LTS Int Bool where
  Tr s label s' := (label = false ∧ s' = s) ∨ (label = true ∧ s' = 0)

def readId : Int -> Int := fun s => s

def transferToy : Bool -> Sign -> Sign
  | false, a => a
  | true, _ => .zero

theorem stepSoundToy :
    SignStepSound toyLTS readId transferToy := by
  intro label a s s' hs htr
  rcases htr with hKeep | hZero
  · rcases hKeep with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simpa [gammaSignState, readId, transferToy] using hs
  · rcases hZero with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simp [readId, transferToy, gammaSign]

example :
    SoundStep (postStep toyLTS) (gammaSignState readId) transferToy := by
  exact soundStep_postStep_sign_of_stepSound toyLTS readId transferToy stepSoundToy

def toySignAbstraction : LTSAbstraction Int Bool Sign :=
  signAbstractionOfStepSound toyLTS readId transferToy stepSoundToy

example :
    SoundTrace
      (liftTracePost (postStep toyLTS))
      (gammaSignState readId)
      (liftTracePostSharp transferToy) := by
  exact toySignAbstraction.soundTraceLifted

end InstancesLTSSignHook
end Tests
