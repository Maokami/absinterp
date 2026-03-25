import Examples.IMP.Analysis.Interval
import Examples.IMP.Pretty

/-!
# Widening-based Interval analysis for a looping IMP program

Demonstrates the framework widening interfaces (`pfp`, `WAcc`,
`WidenUpperBound`) on a simple while-loop IMP program analyzed with
the Interval domain.

## Program

```
x0 := 0;
while x1 do
  x0 := x0 + 1
```

## Approach

A finite 4-element domain tracks the Interval progression of `x0` at the
loop head: `⊥ → [0,0] → [0,1] → ⊤`. Each element maps to a concrete
`Interval` via `toInterval`, connecting to the Interval domain's
concretization. Widening jumps to `⊤` when bounds change, exactly
matching the aggressive `widenInterval` strategy.

The framework `pfp` computes a post-fixpoint in two widening steps,
and `isPostFixpoint_pfp` certifies the result.
-/

namespace Examples.IMP.Programs

open AbsInterpLTS.Domains
open AbsInterpLTS.Framework.Iteration

/-! ## The IMP program -/

/-- The IMP program analyzed with widening. -/
def widenShowcase : Stmt := [imp|
  x0 := 0 ;;
  while x1 do
    x0 := x0 + 1
]

/-! ## Finite loop domain

A 4-element domain tracking the Interval progression of `x0` during
widened iteration. Follows the `Flat3` test pattern. -/

/-- Finite abstraction of `x0` at the while-loop head. -/
inductive LoopAbs where
  | bot
  | zero     -- represents [0, 0]
  | zeroOne  -- represents [0, 1]
  | top
  deriving DecidableEq, Repr

namespace LoopAbs

/-- Map to the Interval domain. -/
def toInterval : LoopAbs → Interval
  | .bot => .bot
  | .zero => AbsInterpLTS.Domains.mk 0 0
  | .zeroOne => AbsInterpLTS.Domains.mk 0 1
  | .top => .top

/-- Concretization via Interval. -/
def gamma (a : LoopAbs) : Set Int :=
  gammaInterval (toInterval a)

/-- Flat order. -/
def le : LoopAbs → LoopAbs → Prop
  | .bot, _ => True
  | .zero, .zero => True
  | .zero, .top => True
  | .zeroOne, .zeroOne => True
  | .zeroOne, .top => True
  | .top, .top => True
  | _, _ => False

instance : DecidableRel le := by
  intro a b; cases a <;> cases b <;> simp [le] <;> exact inferInstance

theorem le_refl : ∀ a : LoopAbs, le a a := by
  intro a; cases a <;> simp [le]

/-- Gamma monotonicity. -/
theorem gamma_mono : ∀ {a b : LoopAbs}, le a b → gamma a ⊆ gamma b := by
  intro a b hab
  cases a <;> cases b <;> simp_all [le, gamma, toInterval, gammaInterval, AbsInterpLTS.Domains.mk]

/--
Abstract loop body transfer: models `x0 := x0 + 1`.

- `f(bot) = zero`: initial entry sets x0 = 0, joined with body(bot) = bot
- `f(zero) = zeroOne`: join([0,0], [0,0]+1) = join([0,0], [1,1]) = [0,1]
- `f(zeroOne) = top`: join([0,0], [0,1]+1) = join([0,0], [1,2]) = [0,2], but
  [0,2] is not in our finite domain, so we over-approximate as ⊤
- `f(top) = top`: join([0,0], ⊤+1) = ⊤
-/
def f : LoopAbs → LoopAbs
  | .bot => .zero
  | .zero => .zeroOne
  | .zeroOne => .top
  | .top => .top

/-- `f` is sound: concrete computation stays within `gamma (f a)`. -/
theorem f_sound (a : LoopAbs) :
    ∀ n ∈ gamma a, (n + 1) ∈ gamma (f a) ∧ (0 : Int) ∈ gamma (f a) := by
  intro n hn
  cases a <;> simp_all [f, gamma, toInterval, gammaInterval, AbsInterpLTS.Domains.mk]
  all_goals omega

/-- Widening: jump to ⊤ unless equal. -/
def w : Widen LoopAbs
  | a, b => if a == b then a else .top

theorem w_upper_bound : WidenUpperBound le w where
  left := by
    intro a b; by_cases h : a == b
    · simp [w, h]; cases a <;> simp [le, BEq.beq, decide_eq_true_eq] at h ⊢
    · simp [w, h]; cases a <;> simp [le]
  right := by
    intro a b; by_cases h : a == b
    · simp [w, h]; cases a <;> cases b <;> simp_all [le, BEq.beq]
    · simp [w, h]; cases b <;> simp [le]

/-- WAcc witness: 2 widening steps suffice. -/
def wacc : WAcc le f w .bot .bot := by
  apply WAcc.intro; intro _ _
  apply WAcc.intro; intro _ _
  apply WAcc.intro; intro _ h
  exact absurd (le_refl (f .top)) h

theorem hBot : ∀ a : LoopAbs, le .bot a := by
  intro a; cases a <;> simp [le]

/-- Compute post-fixpoint via framework `pfp`. -/
def loopPfp : LoopAbs :=
  pfp (inferInstance) w_upper_bound .bot hBot wacc

/-- The computed result is ⊤. -/
theorem loopPfp_eq_top : loopPfp = .top := by native_decide

/-- The result is a genuine post-fixpoint: `f(result) ≤ result`. -/
theorem loopPfp_isPostFixpoint :
    IsPostFixpoint le f loopPfp :=
  isPostFixpoint_pfp (inferInstance) w_upper_bound .bot hBot wacc

end LoopAbs

end Examples.IMP.Programs
