import Mathlib.Tactic.Linter
import AbsInterp

-- Run Mathlib's registered linters on all AbsInterp declarations.
-- Failures here indicate missing docstrings, unused arguments, or
-- simp-lemma normal-form violations in upstream-candidate code.
#lint
