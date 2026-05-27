import Cslib.Init

import AbsInterp
import Examples

/-!
# Axiom-cleanliness guard for upstream-candidate theorems

The reusable soundness path (Framework → Instances/LTS → IMP step
soundness) must use only standard axioms: `propext`, `Quot.sound`,
`Classical.choice`. The non-standard compiler-trusting axioms
`Lean.ofReduceBool` and `Lean.trustCompiler` (introduced by
`native_decide`) must not appear.

`Classical.choice` is expected and acceptable — it arises from
classical reasoning in set-membership proofs, not from unsafe reduction.

Each `#guard_msgs` block below pins the exact axiom set. If a future
change introduces a new axiom dependency (e.g., via `native_decide`),
the mismatch will cause a compile-time error and fail CI.
-/

/-! ## Framework -/

/-- info: 'AbsInterp.Framework.soundTrace_of_soundStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms AbsInterp.Framework.soundTrace_of_soundStep

/-- info: 'AbsInterp.Framework.sound_weak_of_sound_closure' does not depend on any axioms -/
#guard_msgs in #print axioms AbsInterp.Framework.sound_weak_of_sound_closure

/-- info: 'AbsInterp.Framework.soundStep_weak_of_soundStep_closure' does not depend on any axioms -/
#guard_msgs in #print axioms AbsInterp.Framework.soundStep_weak_of_soundStep_closure

/-- info: 'AbsInterp.Framework.omegaReachable_subset_iUnion_kleeneNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms AbsInterp.Framework.omegaReachable_subset_iUnion_kleeneNat

/-! ## Instances/LTS -/

/-- info: 'AbsInterp.Instances.LTS.LTSAbstraction.soundTraceLifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AbsInterp.Instances.LTS.LTSAbstraction.soundTraceLifted

/-- info: 'AbsInterp.Instances.LTS.tauClosureOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AbsInterp.Instances.LTS.tauClosureOp

/-- info: 'AbsInterp.Instances.LTS.sound_reachTransferAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AbsInterp.Instances.LTS.sound_reachTransferAny

/--
info: 'AbsInterp.Instances.LTS.omegaReachableLTS_subset_iUnion_kleeneNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms AbsInterp.Instances.LTS.omegaReachableLTS_subset_iUnion_kleeneNat

/-! ## Examples/IMP — Generic collecting -/

/-- info: 'Examples.IMP.sound_impReachTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.sound_impReachTransfer

/-! ## Examples/IMP — Sign -/

/-- info: 'Examples.IMP.soundStep_impSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.soundStep_impSign

/-- info: 'Examples.IMP.impSignAbstraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.impSignAbstraction

/-! ## Examples/IMP — Interval -/

/-- info: 'Examples.IMP.soundStep_impInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.soundStep_impInterval

/-- info: 'Examples.IMP.impIntervalAbstraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.impIntervalAbstraction

/-! ## Examples/IMP — Parity -/

/-- info: 'Examples.IMP.soundStep_impParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.soundStep_impParity

/-- info: 'Examples.IMP.impParityAbstraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.IMP.impParityAbstraction
