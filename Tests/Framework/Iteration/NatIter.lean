import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkIterationNatIter

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Iteration

def postAddZero : Post Nat :=
  fun states => states ∪ {0}

theorem postAddZero_monotone : MonotonePost postAddZero := by
  intro s t hSubset x hx
  rcases hx with hs | hz
  · exact Or.inl (hSubset hs)
  · exact Or.inr hz

def postAddZeroCollecting : CollectingStep Nat where
  post := postAddZero
  monotone := postAddZero_monotone

example (init1 init2 : Set Nat) (hInit : init1 ⊆ init2) (n : Nat) :
    iterateNat postAddZero init1 n ⊆ iterateNat postAddZero init2 n := by
  exact iterateNat_monotone_init (next := postAddZero) postAddZero_monotone n hInit

example (init : Set Nat) (n : Nat) :
    postAddZeroCollecting.kleeneNat init n ⊆
      postAddZeroCollecting.kleeneNat init (n + 1) := by
  exact postAddZeroCollecting.kleeneNat_chain_step n init

example (init : Set Nat) (m n : Nat) (hLe : m ≤ n) :
    postAddZeroCollecting.kleeneNat init m ⊆
      postAddZeroCollecting.kleeneNat init n := by
  exact postAddZeroCollecting.kleeneNat_chain_of_le hLe init

example (init states : Set Nat) :
    postAddZeroCollecting.reachF init states = init ∪ postAddZero states := by
  rfl

example (cfg : CollectingStep Nat) (init : Set Nat) (n : Nat) :
    init ⊆ cfg.kleeneNat init (n + 1) := by
  exact cfg.init_subset_kleeneNat_succ n init

inductive OneAbs where
  | top
  deriving DecidableEq, Repr

def gammaOne : OneAbs -> Set Nat
  | .top => Set.univ

def postId : Post Nat :=
  fun states => states

def postSharpId : PostSharp OneAbs :=
  fun a => a

theorem sound_postId : Sound postId gammaOne postSharpId := by
  intro a s hs
  simp [postId, gammaOne] at hs
  simpa using hs

theorem postId_monotone : MonotonePost postId := by
  intro s t hSubset
  simpa [postId] using hSubset

example (n : Nat) :
    iterateNat postId (gammaOne OneAbs.top) n ⊆
      gammaOne (iterateNatSharp postSharpId OneAbs.top n) := by
  exact sound_iterateNat_of_sound
    (next := postId)
    (gamma := gammaOne)
    (nextSharp := postSharpId)
    sound_postId
    postId_monotone
    n
    OneAbs.top

end FrameworkIterationNatIter
end Tests
