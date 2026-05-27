import Cslib.Init

import AbsInterp

namespace Tests
namespace InstancesLTSParityHook

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Instances.LTS
open AbsInterp.Instances.LTS.Analyses

def toyLTS : Cslib.LTS Int Bool where
  Tr s label s' := (label = false ∧ s' = s) ∨ (label = true ∧ s' = 0)

def readId : Int -> Int := fun s => s

def transferToy : Bool -> Parity -> Parity
  | false, a => a
  | true, _ => .even

theorem stepSoundToy :
    ParityStepSound toyLTS readId transferToy := by
  intro label a s s' hs htr
  rcases htr with hKeep | hZero
  · rcases hKeep with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simpa [gammaParityState, readId, transferToy] using hs
  · rcases hZero with ⟨hLabel, hEq⟩
    subst hLabel
    subst hEq
    simp [readId, transferToy, gammaParity]

example :
    SoundStep (postStep toyLTS) (gammaParityState readId) transferToy := by
  exact soundStep_postStep_parity_of_stepSound toyLTS readId transferToy stepSoundToy

def toyParityAbstraction : LTSAbstraction Int Bool Parity :=
  parityAbstractionOfStepSound toyLTS readId transferToy stepSoundToy

example :
    SoundTrace
      (liftTracePost (postStep toyLTS))
      (gammaParityState readId)
      (liftTracePostSharp transferToy) := by
  exact toyParityAbstraction.soundTraceLifted

end InstancesLTSParityHook
end Tests
