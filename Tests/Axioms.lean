import Cslib.Init

import AbsInterpLTS
import Examples

/-!
Axiom-cleanliness reference for upstream-candidate theorems.

The reusable soundness path (Framework → Instances/LTS → IMP step
soundness) must use only standard axioms: `propext`, `Quot.sound`,
`Classical.choice`. The non-standard compiler-trusting axioms
`Lean.ofReduceBool` and `Lean.trustCompiler` (introduced by
`native_decide`) must not appear.

`Classical.choice` is expected and acceptable — it arises from
classical reasoning in set-membership proofs, not from unsafe reduction.

Run `lake build Tests` and inspect the output, or use the `lean_verify`
MCP tool, to confirm axiom cleanliness of these theorems.
-/

-- Framework: step soundness lifts to trace soundness (upstream candidate)
#print axioms AbsInterpLTS.Framework.soundTrace_of_soundStep

-- Instances/LTS: LTSAbstraction packages the lifting (upstream candidate)
#print axioms AbsInterpLTS.Instances.LTS.LTSAbstraction.soundTraceLifted

-- IMP: one-step soundness of the generic Sign transfer (upstream candidate)
#print axioms Examples.IMP.soundStep_impSign

-- IMP: full Sign LTS abstraction packaging (upstream candidate)
#print axioms Examples.IMP.impSignAbstraction

-- IMP: one-step soundness of the generic Interval transfer (upstream candidate)
#print axioms Examples.IMP.soundStep_impInterval

-- IMP: full Interval LTS abstraction packaging (upstream candidate)
#print axioms Examples.IMP.impIntervalAbstraction
