import VersoManual

open Verso.Genre Manual

#doc (Manual) "IMP Collecting Showcase" =>
%%%
tag := "imp-collecting-showcase"
%%%

This chapter walks through the stronger IMP collecting case study.
The authoritative Lean source is
[`Examples/IMP/Programs/CollectingShowcase.lean`](https://github.com/Maokami/absinterp/blob/main/Examples/IMP/Programs/CollectingShowcase.lean).

# The program

```
x0 := 5 ;;
while x0 do
  x0 := x0 + 0
```

Concretely: set `x0` to `5`, then loop forever re-assigning `x0 := x0 + 0`
as long as `x0 ≠ 0`. Because the body leaves `x0` unchanged and the loop
entry pins `x0` to `5`, every infinite execution from any initial store
keeps `x0 = 5` from the first iteration onward.

This program is chosen because it is

- *divergent*, so it fits the `omegaReachableLTS` story directly;
- *arithmetically non-trivial*, exercising branch filtering,
  expression evaluation, the addition transfer, and store update;
- *tight enough* that a hand-written exact interval post-fixpoint
  `x0 = [5, 5]` exists and is closed under every transfer.

It is deliberately stronger than a `ActiveIn`-only structural smoke test
and weaker than anything requiring widening — a clean spot to exercise
the generic collecting/fixpoint bridge end to end.

# What is proved

The headline theorem is

```
theorem x0_eq_5_at_wloop (σ : Store)
    (hOmega : (wloop, σ) ∈ omegaReachableLTS impLTS init) :
    σ Var.x0 = 5
```

Read: every state reachable on an infinite execution from the initial
set, whose control is at the while head `wloop`, has `x0 = 5`.

The `init` set is `{ c | controlOfConfig c = program }` — any concrete
store, at the program's entry control. The invariant is therefore
genuinely about concrete program states, not about the abstract domain
alone.

# How the proof is structured

The proof consumes the Session 4/5 infrastructure.

- A hand-written abstract post-fixpoint `fix : ConfigSharp Interval`
  assigns `x0 = [5, 5]` at the three loop-related active controls
  (`.seq .skip wloop`, `wloop`, `.seq body wloop`) and `⊤` everywhere
  else.
- `init_subset_gamma : init ⊆ gammaProgramInterval program fix` — the
  initial set lives at the program entry control where `fix = ⊤`, so
  any initial store is admitted.
- `fix_isPostFixpoint :
   IsPostFixpoint (· ≤ ·) (impIntervalReachTransfer program fix) fix`
  — the central content. Proved pointwise: outside
  `(control, x0) ∈ {B, C, D} × {Var.x0}` the bound is trivial
  (`fix = ⊤`); the three non-trivial evaluations of
  `transferAnyProgram intervalAnalysisDomain program fix` reduce by
  structural unfolding + `Pi.sup_apply` to `mk 5 5 = mk 5 5`.
- `omegaReachableLTS_subset_of_isPostFixpoint_impInterval` is the
  Session 5 bridge specialised to the Interval IMP collecting
  abstraction. It composes
  `omegaReachableLTS_subset_omegaReachable` with the generic
  fixpoint theorem `omegaReachable_subset_of_isPostFixpoint` and
  delivers `omegaReachableLTS impLTS init ⊆ gammaProgramInterval program fix`.
- Extracting `σ Var.x0 ∈ gammaInterval (mk 5 5) = {5}` at the
  `wloop` control finishes with `omega`.

# Why it matters

This is the first IMP artifact in the repository that is

- *axiom-clean* — the proof avoids `native_decide` entirely. The
  critical `transferAny_at_{B,C,D}_x0` lemmas unfold
  `transferAnyProgram` structurally and finish with `rfl`, which means
  the flagship collecting theorem stays on the upstream-candidate axiom
  path (`propext`, `Quot.sound`, `Classical.choice`).
- *materially about values*, not just control. `ActiveIn`-only
  invariants say the executions stay inside the program; this one
  says `x0` takes a specific integer value at a specific control
  point.
- *a genuine consumer* of both Session 4 (generic fixpoint bridge)
  and Session 5 (LTS collecting adapter), exercising the IMP adapter
  (Session 6) and the per-domain Interval wrappers in between.

As a case study, it gives the framework an end-to-end demo with a
concrete, checkable conclusion — the natural next escalation from the
earlier widening and labeled-trace showcases.

# Related artifacts

- `Examples/IMP/Programs/Showcase.lean` — labeled Sign trace analysis,
  a flagship for the trace path.
- `Examples/IMP/Programs/WidenShowcase.lean` — widening/`pfp` on a
  small Interval-based `Flat3` lattice.
- `Examples/IMP/Programs/LoopShowcase.lean` — an earlier Sign-based
  countdown loop demo, now structurally subsumed by the stronger
  Interval case.
