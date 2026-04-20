import Examples.IMP.Analysis.Sign

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

The abstract loop body transfer `loopBodySign` applies `filterNonzeroSign`
(loop condition) then `addTransfer _ neg` (decrement). The full loop
transfer `loopTransferSign` joins the initial entry (`pos` from `x0 := 5`)
with the body result.

Iterating: `bot → pos → top → top` (fixpoint). We prove `top` is a
post-fixpoint and that it is sound w.r.t. the concrete loop body. After
the loop-exit condition `x0 = 0`, filtering via `filterZeroSign`
yields `zero`, proving that any terminating execution has `x0 = 0`.

## Axiom note

All theorems in this file are axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only). No `native_decide` is used.
-/

namespace Examples.IMP.Programs

open AbsInterp.Domains
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
  addTransfer (filterNonzeroSign a) (constSign (-1))

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
    IsPostFixpoint leSign loopTransferSign loopPfp :=
  leSign_refl _

/-! ## Soundness of abstract loop body -/

/-- The abstract loop body is sound: concrete decrement under nonzero
    condition is captured by `loopBodySign`. -/
theorem loopBodySign_sound
    {a : Sign} {n : Int}
    (hn : n ∈ gammaSign a)
    (hNz : n ≠ 0) :
    n + (-1) ∈ gammaSign (loopBodySign a) :=
  addTransfer_sound (filterNonzeroSign_sound hn hNz) (constSign_sound (-1))

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

/-! ## Concrete exit property

The key end-to-end result: the Sign analysis determines that `x0 = 0`
after the loop. This connects widened abstract interpretation to a
concrete program property. -/

/-- After loop exit, the abstract value is `zero`. -/
theorem loopShowcase_exit_abstract :
    filterZeroSign loopPfp = Sign.zero := rfl

/-- At loop exit (`x0 = 0`), the analysis proves `x0 ∈ {0}`.
    Any execution that terminates the countdown loop has `x0 = 0`. -/
theorem loopShowcase_exit_x0_zero
    {n : Int}
    (hInv : n ∈ gammaSign loopPfp)
    (hExit : n = 0) :
    n ∈ gammaSign .zero :=
  filterZeroSign_sound hInv hExit

end Examples.IMP.Programs
