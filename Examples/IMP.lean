import Examples.IMP.Syntax
import Examples.IMP.Pretty
import Examples.IMP.Semantics
import Examples.IMP.Abstraction
import Examples.IMP.Analysis
import Examples.IMP.LTS
import Examples.IMP.Programs

/-!
The IMP example suite is organized in four layers:

- `Syntax` / `Pretty`: the surface language used in examples
- `Semantics` / `Abstraction` / `LTS`: the canonical IMP state space and LTS
- `Analysis`: generic abstract interpreters over the canonical IMP LTS
- `Programs`: tutorial mini-examples plus the flagship end-to-end showcase
-/
