import Cslib.Init

import AbsInterpLTS
import Examples

/-!
Axiom-cleanliness reference for upstream-candidate theorems.

The reusable soundness path (Framework → Instances/LTS → IMP step
soundness) must use only standard axioms: `propext`, `Quot.sound`,
`Classical.choice`. No `Lean.ofReduceBool` or `Lean.trustCompiler`.

Run `lake build Tests` and inspect the output, or use the `lean_verify`
MCP tool, to confirm axiom cleanliness of these theorems.
-/

-- Framework: step soundness lifts to trace soundness (upstream candidate)
#print axioms AbsInterpLTS.Framework.soundTrace_of_soundStep

-- Instances/LTS: LTSAbstraction packages the lifting (upstream candidate)
#print axioms AbsInterpLTS.Instances.LTS.LTSAbstraction.soundTraceLifted

-- IMP: one-step soundness of the generic Sign transfer (upstream candidate)
#print axioms Examples.IMP.soundStep_impSign

-- IMP: full LTS abstraction packaging (upstream candidate)
#print axioms Examples.IMP.impSignAbstraction
