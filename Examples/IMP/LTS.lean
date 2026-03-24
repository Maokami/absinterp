import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import Examples.IMP.Semantics

namespace Examples.IMP

/--
The canonical labeled small-step LTS for IMP.

This general LTS covers all IMP programs and is the intended surface for
generic abstract analyses. Program-specific examples remain under
`Examples.IMP.Programs` as small case studies, but the generic IMP LTS is the
preferred entry point for framework experiments.
-/
def impLTS : Cslib.LTS Config StepLabel where
  Tr c μ c' := Step c μ c'

end Examples.IMP
