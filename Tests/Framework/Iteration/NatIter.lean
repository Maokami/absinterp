import Cslib.Init

import AbsInterpLTS

namespace Tests
namespace FrameworkIterationNatIter

open AbsInterpLTS
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Iteration

def postAddZero : Post Nat :=
  fun states => states ∪ {0}

theorem postAddZero_monotone : MonotonePost postAddZero := by
  intro s t hSubset x hx
  rcases hx with hs | hz
  · exact Or.inl (hSubset hs)
  · exact Or.inr hz

theorem postAddZero_inflationary : InflationaryPost postAddZero := by
  intro states x hx
  exact Or.inl hx

example (init1 init2 : Set Nat) (hInit : init1 ⊆ init2) (n : Nat) :
    iterateNat postAddZero init1 n ⊆ iterateNat postAddZero init2 n := by
  exact iterateNat_monotone_init (next := postAddZero) postAddZero_monotone n hInit

example (init : Set Nat) (m n : Nat) (hLe : m ≤ n) :
    iterateNat postAddZero init m ⊆ iterateNat postAddZero init n := by
  exact iterateNat_chain_of_le
    (next := postAddZero)
    postAddZero_monotone
    postAddZero_inflationary
    hLe
    init

example (init states : Set Nat) :
    reachF init postAddZero states = init ∪ postAddZero states := by
  rfl

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
