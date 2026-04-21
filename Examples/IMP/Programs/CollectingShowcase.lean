import Examples.IMP.Analysis.Sign
import Examples.IMP.Analysis.Interval

/-!
# IMP Collecting/Fixpoint Showcase

Canonical IMP case study for the generic collecting/fixpoint path. Unlike
`LoopShowcase` and `WidenShowcase`, this file consumes the Session 4/5
bridge infrastructure end-to-end:

- builds on `impSignCollectingTransfer` and `impSignReachTransfer`
- discharges a post-fixpoint at the abstract level
- concludes an ω-reachability safety property via
  `omegaReachableLTS_subset_of_isPostFixpoint_impSign`

The showcase uses a simple always-looping program (`while 1 do skip`) so
that the concrete set of ω-executions is non-trivial. The post-fixpoint is
the pointwise-top abstract state, which is valid without computing a
tighter invariant. The conclusion is a genuine control-flow property:

> every ω-reachable state has a control location that is active in the
> source program (i.e., executions do not escape the program's structure).

This exercises the whole Session 4/5 bridge through the IMP adapter layer
without requiring a hand-computed non-trivial post-fixpoint.
-/

namespace Examples.IMP.Programs
namespace CollectingShowcase

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework
open AbsInterp.Framework.Iteration
open AbsInterp.Instances.LTS
open Examples.IMP

/-- Always-looping IMP program: `while 1 do skip`. -/
def program : Stmt := .while (.lit 1) .skip

/-- Initial concrete state set: configs starting at the program's entry. -/
def init : Set Config := { c | controlOfConfig c = program }

/-- Pointwise-top abstract post-fixpoint. -/
def fix : ConfigSharp Sign := fun _ _ => ⊤

/-- The top fix over-approximates the initial set. -/
theorem init_subset_gamma :
    init ⊆ gammaProgramSign program fix := by
  rintro ⟨s, σ⟩ hc
  have hS : s = program := hc
  subst hS
  refine ⟨ActiveIn.self _, ?_⟩
  intro _
  exact Set.mem_univ _

/-- `fix` is a post-fixpoint of the Sign reach transfer with initAbs = fix. -/
theorem fix_isPostFixpoint :
    IsPostFixpoint (· ≤ ·) (impSignReachTransfer program fix) fix := by
  intro s x
  exact le_top

/--
Headline: every ω-reachable state from the initial set has an
`ActiveIn`-valid control location.

Proof route:
  `init ⊆ gammaProgramSign program fix`
  + `fix` is a post-fixpoint
  →  (via `omegaReachableLTS_subset_of_isPostFixpoint_impSign`)
  →  `omegaReachableLTS impLTS init ⊆ gammaProgramSign program fix`
  →  extract the `ActiveIn` component.
-/
theorem omega_active_control :
    ∀ c ∈ omegaReachableLTS impLTS init,
      ActiveIn program (controlOfConfig c) := by
  intro c hc
  have hGamma : c ∈ gammaProgramSign program fix :=
    omegaReachableLTS_subset_of_isPostFixpoint_impSign
      program init fix fix init_subset_gamma fix_isPostFixpoint hc
  exact hGamma.1

/-- Kleene corollary: every finite Kleene iterate stays within the program's
control structure. -/
theorem kleeneNat_active_control :
    ∀ n, ∀ c ∈ (postAny_collectingStep impLTS).kleeneNat init n,
      ActiveIn program (controlOfConfig c) := by
  intro n c hc
  have hGamma : c ∈ gammaProgramSign program fix :=
    kleeneNat_subset_of_isPostFixpoint_impSign
      program init fix fix init_subset_gamma fix_isPostFixpoint n hc
  exact hGamma.1

end CollectingShowcase
end Examples.IMP.Programs
