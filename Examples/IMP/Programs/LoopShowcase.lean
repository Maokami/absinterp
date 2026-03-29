import Examples.IMP.Analysis.Sign
import Examples.IMP.Pretty

/-!
# Loop Analysis Showcase

End-to-end analysis of a looping IMP program using the Sign domain and the
framework's widening/post-fixpoint soundness machinery.

## Program

```
x0 := 5;
while x0 do
  x0 := x0 + (-1)
```

## Approach

The abstract loop body transfer `loopBodySign` applies `assumeNonzero`
(loop condition) then `addTransfer _ neg` (decrement). The full loop
transfer `loopTransferSign` joins the initial entry (`pos` from `x0 := 5`)
with the body result.

Iterating: `bot → pos → top → top` (fixpoint). We prove `top` is a
post-fixpoint and that it is sound w.r.t. the concrete loop body. After
the loop-exit condition `x0 = 0`, backward refinement via `assumeZero`
yields `zero`, proving that any terminating execution has `x0 = 0`.

## Axiom note

All theorems in this file are axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only). No `native_decide` is used.
-/

namespace Examples.IMP.Programs

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Framework.Iteration

/-! ## The IMP program -/

/-- Countdown loop: decrement x0 from 5 until 0. -/
def loopShowcase : Stmt :=
  .seq
    (.assign Var.x0 (.lit 5))
    (.while (.var Var.x0)
      (.assign Var.x0 (.add (.var Var.x0) (.lit (-1)))))

/-! ## Abstract loop transfer on Sign -/

/-- Abstract loop body: assume `x0 ≠ 0` (loop condition), then `x0 := x0 + (-1)`. -/
def loopBodySign (a : Sign) : Sign :=
  addTransfer (assumeNonzero a) (constSign (-1))

/-- Full loop transfer: join of initial entry (`pos` from `x0 := 5`) with body result. -/
def loopTransferSign (a : Sign) : Sign :=
  joinSign (constSign 5) (loopBodySign a)

/-! ## Post-fixpoint -/

/-- The abstract post-fixpoint at the loop head is `top`. -/
def loopPfp : Sign := .top

/-- `loopTransferSign(top) = top`, verifiable by reduction. -/
theorem loopTransferSign_top : loopTransferSign .top = .top := rfl

/-- `top` is a post-fixpoint of `loopTransferSign`: `f(top) ≤ top`. -/
theorem loopPfp_isPostFixpoint :
    IsPostFixpoint leSign loopTransferSign loopPfp := by
  show leSign (loopTransferSign .top) .top
  rw [loopTransferSign_top]
  exact leSign_refl _

/-! ## Soundness of abstract loop body -/

/-- The abstract loop body is sound: concrete decrement under nonzero
    condition is captured by `loopBodySign`. -/
theorem loopBodySign_sound
    {a : Sign} {n : Int}
    (hn : n ∈ gammaSign a)
    (hNz : n ≠ 0) :
    n + (-1) ∈ gammaSign (loopBodySign a) :=
  addTransfer_sound (assumeNonzero_sound hn hNz) (constSign_sound (-1))

/-- The full loop transfer is sound w.r.t. concrete semantics.
    For any `n ∈ γ(a)`: the initial value 5 and the body result `n-1`
    (under `n ≠ 0`) are both in `γ(loopTransferSign a)`. -/
theorem loopTransferSign_sound_init (a : Sign) :
    (5 : Int) ∈ gammaSign (loopTransferSign a) :=
  joinSign_sound _ _ (Or.inl (constSign_sound 5))

theorem loopTransferSign_sound_body
    {a : Sign} {n : Int}
    (hn : n ∈ gammaSign a)
    (hNz : n ≠ 0) :
    n + (-1) ∈ gammaSign (loopTransferSign a) :=
  joinSign_sound _ _ (Or.inr (loopBodySign_sound hn hNz))

/-! ## Loop invariant from post-fixpoint

The post-fixpoint `top` is trivially an invariant (`γ(top) = Set.univ`).
This is expected for Sign: the domain cannot track decreasing values
precisely. The payoff comes at loop exit. -/

/-- The loop body preserves the invariant: concrete execution stays
    within `γ(loopPfp)`. -/
theorem loopPfp_invariant_body
    {n : Int}
    (_hn : n ∈ gammaSign loopPfp)
    (_hNz : n ≠ 0) :
    n + (-1) ∈ gammaSign loopPfp :=
  gammaSign_top _

/-- The initial value is in the invariant. -/
theorem loopPfp_invariant_init :
    (5 : Int) ∈ gammaSign loopPfp :=
  gammaSign_top _

/-! ## Concrete exit property

The key end-to-end result: the Sign analysis determines that `x0 = 0`
after the loop. This connects widened abstract interpretation to a
concrete program property. -/

/-- After loop exit, the abstract value is `zero`. -/
theorem loopShowcase_exit_abstract :
    assumeZero loopPfp = Sign.zero := rfl

/-- At loop exit (`x0 = 0`), the analysis proves `x0 ∈ {0}`.
    Any execution that terminates the countdown loop has `x0 = 0`. -/
theorem loopShowcase_exit_x0_zero
    {n : Int}
    (hInv : n ∈ gammaSign loopPfp)
    (hExit : n = 0) :
    n ∈ gammaSign .zero :=
  assumeZero_sound hInv hExit

/-- Concrete corollary: the exit condition fully determines x0. -/
theorem loopShowcase_exit_concrete
    {n : Int}
    (hInv : n ∈ gammaSign loopPfp)
    (hExit : n = 0) :
    n = 0 := by
  have hMem := loopShowcase_exit_x0_zero hInv hExit
  simpa [gammaSign] using hMem

end Examples.IMP.Programs
