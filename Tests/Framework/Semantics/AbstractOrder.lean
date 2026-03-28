import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkSemanticsAbstractOrder

open AbsInterp
open AbsInterp.Framework

def stepId : StepPost Nat Bool :=
  fun _ states => states

example : TracePost Nat Bool := liftTracePost stepId

def addOne : PostSharp Nat :=
  fun n => n + 1

def addTwo : PostSharp Nat :=
  fun n => n + 2

theorem addOne_monotone : MonotonePostSharp addOne := by
  intro a b hAB
  simpa [addOne] using Nat.succ_le_succ hAB

theorem addTwo_monotone : MonotonePostSharp addTwo := by
  intro a b hAB
  simpa [addTwo] using Nat.add_le_add_right hAB 2

example : MonotonePostSharp (fun n : Nat => n) :=
  MonotonePostSharp.id

example : MonotonePostSharp (composePostSharp addOne addTwo) :=
  MonotonePostSharp.compose addOne_monotone addTwo_monotone

def gammaTop : Unit -> Set Nat :=
  fun _ => Set.univ

def postId : Post Nat :=
  fun states => states

def postSharpUnit : PostSharp Unit :=
  fun _ => ()

theorem sound_postId_unit : Sound postId gammaTop postSharpUnit := by
  intro _ s hs
  simp [postId, gammaTop] at hs ⊢

def stepPostId : StepPost Nat Bool :=
  fun _ => postId

def stepSharpUnit : StepPostSharp Unit Bool :=
  fun _ => postSharpUnit

example : SoundStep stepPostId gammaTop stepSharpUnit := by
  intro _ _ s hs
  simp [stepPostId, postId, gammaTop] at hs ⊢

end FrameworkSemanticsAbstractOrder
end Tests
