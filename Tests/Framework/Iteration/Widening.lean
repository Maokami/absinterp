import Cslib.Init

import AbsInterp

namespace Tests
namespace FrameworkIterationWidening

open AbsInterp.Framework
open AbsInterp.Framework.Iteration

/-! # Flat3 smoke test for widening/narrowing interfaces

A toy 3-element flat lattice `{bot, mid, top}` exercising
`WAcc`, `witer`, `pfp`, `IsPostFixpoint`, and `sound_of_isPostFixpoint`.
-/

/-- Three-element flat lattice. -/
inductive Flat3 where
  | bot
  | mid
  | top
  deriving DecidableEq, Repr

namespace Flat3

/-- Flat order on `Flat3`. -/
def le : Flat3 -> Flat3 -> Prop
  | .bot, _ => True
  | .mid, .mid => True
  | .mid, .top => True
  | .top, .top => True
  | _, _ => False

instance : DecidableRel le := by
  intro a b
  cases a <;> cases b <;> simp [le] <;> exact inferInstance

theorem le_refl : ∀ a : Flat3, le a a := by
  intro a; cases a <;> simp [le]

theorem le_trans : ∀ a b c : Flat3, le a b -> le b c -> le a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [le]

/-- Gamma concretization for Flat3 over Nat. -/
def gamma : Flat3 -> Set Nat
  | .bot => ∅
  | .mid => {0}
  | .top => Set.univ

theorem gamma_mono : ∀ {a b : Flat3}, le a b -> gamma a ⊆ gamma b := by
  intro a b hab
  cases a <;> cases b <;> simp_all [le, gamma]

/-- Abstract transfer: bot→mid, mid→top, top→top. -/
def f : Flat3 -> Flat3
  | .bot => .mid
  | .mid => .top
  | .top => .top

/-- Widening: always jump to top (unless both equal). -/
def w : Widen Flat3
  | a, b => if a == b then a else .top

@[simp] theorem w_ne {a b : Flat3} (h : a ≠ b) : w a b = .top := by
  simp [w, h]

@[simp] theorem w_eq {a : Flat3} : w a a = a := by
  simp [w]

theorem w_upper_bound : WidenUpperBound le w where
  left := by
    intro a b
    by_cases h : a = b
    · subst h; simp [le_refl]
    · simp [h]; cases a <;> simp [le]
  right := by
    intro a b
    by_cases h : a = b
    · subst h; simp [le_refl]
    · simp [h]; cases b <;> simp [le]

/-- WAcc witness for the Flat3 example starting from bot. -/
def flat3_acc : WAcc le f w .bot .bot := by
  -- Step 0: x=bot, y=bot. f(bot)=mid, ¬ le mid bot, widen bot mid = top
  apply WAcc.intro
  intro _ _
  -- Step 1: x=mid, y=top. f(top)=top, le top top, so done (vacuously)
  apply WAcc.intro
  intro _ h
  exact absurd (le_refl (f .top)) h

theorem hBot : ∀ a : Flat3, le .bot a := by
  intro a; cases a <;> simp [le]

/-- pfp on the Flat3 example yields top. -/
theorem pfp_eq_top :
    pfp (inferInstance) w_upper_bound .bot hBot flat3_acc = .top := by
  native_decide

/-- pfp result is indeed a post-fixpoint. -/
theorem pfp_is_postfixpoint :
    IsPostFixpoint le f
      (pfp (inferInstance) w_upper_bound .bot hBot flat3_acc) := by
  exact isPostFixpoint_pfp (inferInstance) w_upper_bound .bot hBot flat3_acc

/-- Concrete post: add 0 to the set. -/
def post : Post Nat :=
  fun states => states ∪ {0}

theorem post_monotone : MonotonePost post := by
  intro s t hSubset x hx
  rcases hx with hs | hz
  · exact Or.inl (hSubset hs)
  · exact Or.inr hz

/-- Abstract post is sound w.r.t. concrete post and gamma. -/
theorem post_sound : Sound post gamma (fun _ => Flat3.top) := by
  intro a s hs
  simp [gamma]

/-- Exercise sound_of_isPostFixpoint: top is a post-fixpoint of (fun _ => top),
    so all iterates stay within gamma top = univ. -/
example : ∀ n, iterateNat post (gamma .top) n ⊆ gamma .top := by
  apply sound_of_isPostFixpoint
    (postSharp := fun _ => Flat3.top)
    post_sound post_monotone
    (fun h => gamma_mono h)
  simp [IsPostFixpoint, le]

end Flat3

end FrameworkIterationWidening
end Tests
