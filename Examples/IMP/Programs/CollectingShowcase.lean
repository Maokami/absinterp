import Examples.IMP.Analysis.Sign
import Examples.IMP.Analysis.Interval

/-!
# IMP Collecting/Fixpoint Showcase

Canonical IMP consumer of the collecting/fixpoint bridge.

This file exercises the generic IMP collecting path end-to-end via the
Interval domain, proving a real **value** invariant — every ω-reachable
state of the flagship program has `x0 = 5` at the loop head — rather
than a purely structural `ActiveIn` statement.

## Program

```imp
x0 := 5 ;;
while x0 do
  x0 := x0 + 0
```

## Proof outline

1. Hand-write a `ConfigSharp Interval` post-fixpoint `fix` that assigns
   the exact interval `[5, 5]` to `x0` at every loop-related active
   control location and `⊤` elsewhere.
2. Show `init ⊆ gammaProgramInterval program fix` (the initial set's
   control is `program`, where `fix = ⊤`).
3. Prove `fix` is a post-fixpoint of `impIntervalReachTransfer program fix`
   by direct pointwise case analysis on every (control, variable) pair.
4. Feed the pieces into
   `omegaReachableLTS_subset_of_isPostFixpoint_impInterval` to obtain
   the headline value invariant.

The proof is axiom-clean: it does not use `native_decide`.
-/

namespace Examples.IMP.Programs
namespace CollectingShowcase

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Framework.Iteration
open AbsInterp.Instances.LTS
open Examples.IMP

/-! ## Program components -/

/-- Loop body: `x0 := x0 + 0`. -/
def body : Stmt := .assign Var.x0 (.add (.var Var.x0) (.lit 0))

/-- Loop: `while x0 do x0 := x0 + 0`. -/
def wloop : Stmt := .while (.var Var.x0) body

/-- Flagship program: `x0 := 5 ;; while x0 do x0 := x0 + 0`. -/
def program : Stmt := .seq (.assign Var.x0 (.lit 5)) wloop

/-- Initial concrete set: configs starting at the program's entry. -/
def init : Set Config := { c | controlOfConfig c = program }

/-! ## Candidate post-fixpoint -/

/--
Abstract state mapping every loop-related active control to the exact
interval `[5, 5]` for `x0` and `⊤` for every other variable/control.
-/
def fix : ConfigSharp Interval := fun s x =>
  if s = .seq .skip wloop ∨ s = wloop ∨ s = .seq body wloop then
    if x = Var.x0 then AbsInterp.Domains.mk 5 5 else ⊤
  else
    ⊤

@[simp] private theorem fix_B_x0 :
    fix (.seq .skip wloop) Var.x0 = AbsInterp.Domains.mk 5 5 := by
  simp [fix]

@[simp] private theorem fix_C_x0 :
    fix wloop Var.x0 = AbsInterp.Domains.mk 5 5 := by
  simp [fix, wloop, body]

@[simp] private theorem fix_D_x0 :
    fix (.seq body wloop) Var.x0 = AbsInterp.Domains.mk 5 5 := by
  simp [fix, wloop, body]

/-! ## Initial coverage -/

theorem init_subset_gamma : init ⊆ gammaProgramInterval program fix := by
  rintro ⟨s, σ⟩ hc
  have hS : s = program := hc
  subst hS
  refine ⟨ActiveIn.self _, ?_⟩
  intro y
  have hNotLoop :
      ¬ (program = .seq .skip wloop ∨ program = wloop ∨ program = .seq body wloop) := by
    intro hOr
    rcases hOr with h | h | h <;> simp [program, wloop, body] at h
  have hFix : fix program y = ⊤ := by simp [fix, hNotLoop]
  show σ y ∈ gammaInterval (fix program y)
  rw [hFix]
  exact gammaInterval_top (σ y)

/-! ## Computing `transferAnyProgram` at the relevant pointwise nodes

The generic `transferAnyProgram` for our flagship program evaluates
pointwise at the three `x0`-tracked loop controls to the exact
interval `[5, 5]`. We unfold by structural reduction + `Pi.sup_apply`
and then use the `intervalAnalysisDomain` capability instances'
computation rules (all `rfl`-based) to discharge leaves.
-/

/-- `transferAnyProgram ... fix` at `(.seq .skip wloop, Var.x0)` equals `mk 5 5`. -/
private theorem transferAny_at_B_x0 :
    transferAnyProgram intervalAnalysisDomain program fix (.seq .skip wloop) Var.x0 =
      AbsInterp.Domains.mk 5 5 := by
  simp only [program, wloop, body, transferAnyProgram, transferProgram,
             liftSeqConfig, singletonConfig,
             seqView, evalExpr, Pi.sup_apply]
  rfl

/-- `transferAnyProgram ... fix` at `(wloop, Var.x0)` equals `mk 5 5`. -/
private theorem transferAny_at_C_x0 :
    transferAnyProgram intervalAnalysisDomain program fix wloop Var.x0 =
      AbsInterp.Domains.mk 5 5 := by
  simp only [program, wloop, body, transferAnyProgram, transferProgram,
             liftSeqConfig, singletonConfig,
             seqView, evalExpr, Pi.sup_apply]
  rfl

/-- `transferAnyProgram ... fix` at `(.seq body wloop, Var.x0)` equals `mk 5 5`. -/
private theorem transferAny_at_D_x0 :
    transferAnyProgram intervalAnalysisDomain program fix (.seq body wloop) Var.x0 =
      AbsInterp.Domains.mk 5 5 := by
  simp only [program, wloop, body, transferAnyProgram, transferProgram,
             liftSeqConfig, singletonConfig,
             seqView, evalExpr, Pi.sup_apply]
  rfl

/-! ## Post-fixpoint theorem -/

theorem fix_isPostFixpoint :
    IsPostFixpoint (· ≤ ·) (impIntervalReachTransfer program fix) fix := by
  intro s x
  show (impIntervalReachTransfer program fix fix) s x ≤ fix s x
  show (fix ⊔ transferAnyProgram intervalAnalysisDomain program fix) s x ≤ fix s x
  show fix s x ⊔ transferAnyProgram intervalAnalysisDomain program fix s x ≤ fix s x
  refine sup_le le_rfl ?_
  by_cases hx : x = Var.x0
  swap
  · have : fix s x = ⊤ := by simp [fix, hx]
    rw [this]; exact le_top
  subst hx
  by_cases hLoop : s = .seq .skip wloop ∨ s = wloop ∨ s = .seq body wloop
  swap
  · have : fix s Var.x0 = ⊤ := by simp [fix, hLoop]
    rw [this]; exact le_top
  rcases hLoop with hB | hC | hD
  · subst hB
    rw [transferAny_at_B_x0, fix_B_x0]
  · subst hC
    rw [transferAny_at_C_x0, fix_C_x0]
  · subst hD
    rw [transferAny_at_D_x0, fix_D_x0]

/-! ## Headline value invariant -/

/--
Value invariant: every ω-reachable state with control at the while head
`wloop` has `x0 = 5`.
-/
theorem x0_eq_5_at_wloop (σ : Store)
    (hOmega : (wloop, σ) ∈ omegaReachableLTS impLTS init) :
    σ Var.x0 = 5 := by
  have hGamma : (wloop, σ) ∈ gammaProgramInterval program fix :=
    omegaReachableLTS_subset_of_isPostFixpoint_impInterval
      program init fix fix init_subset_gamma fix_isPostFixpoint hOmega
  have hStore := hGamma.2
  have hx0 : σ Var.x0 ∈ gammaInterval (fix wloop Var.x0) := hStore Var.x0
  rw [fix_C_x0] at hx0
  have hBounds := (mem_gammaInterval_mk_iff 5 5 (σ Var.x0)).mp hx0
  omega

/-! ## Legacy `ActiveIn`-only corollary

The earlier, weaker showcase stayed at the control-flow level. It still
compiles as a secondary smoke test.
-/

theorem legacy_omega_active_control :
    ∀ c ∈ omegaReachableLTS impLTS init,
      ActiveIn program (controlOfConfig c) := by
  intro c hc
  have hGamma : c ∈ gammaProgramInterval program fix :=
    omegaReachableLTS_subset_of_isPostFixpoint_impInterval
      program init fix fix init_subset_gamma fix_isPostFixpoint hc
  exact hGamma.1

end CollectingShowcase
end Examples.IMP.Programs
