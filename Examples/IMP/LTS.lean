import Cslib.Init
import Cslib.Foundations.Semantics.LTS.Basic

import Examples.IMP.Semantics.Defs

namespace Examples.IMP

/--
The IMP language packaged as an unlabeled (`Unit`) LTS.

This general LTS covers all IMP programs and is provided for reference.
For abstract analyses with non-trivial precision, use program-specific LTS
instances (see `Examples.IMP.Programs`).
-/
def impLTS : Cslib.LTS Config Unit where
  Tr c _ c' := Step c c'

end Examples.IMP
