import Cslib.Init

import AbsInterp
import Examples.IMP.Analysis

namespace Tests
namespace FrameworkDomainsCapabilities

open AbsInterp
open AbsInterp.Domains
open AbsInterp.Framework.Domains
open Examples.IMP

/-! ## Smoke tests: reusable domain capabilities -/

example :
    signAnalysisDomain.scalarDomain.gamma (⊥ : Sign) = ∅ := by
  simpa using signAnalysisDomain.gamma_bot

example :
    (0 : Int) ∈ signAnalysisDomain.scalarDomain.gamma (signAnalysisDomain.const 0) := by
  simpa using signAnalysisDomain.const_sound 0

example :
    (0 : Int) ∈
      signAnalysisDomain.scalarDomain.gamma
        (signAnalysisDomain.intersect Sign.nonneg Sign.nonpos) := by
  exact signAnalysisDomain.intersect_sound
    (by
      change (0 : Int) ∈ gammaSign Sign.nonneg
      simp [gammaSign])
    (by
      change (0 : Int) ∈ gammaSign Sign.nonpos
      simp [gammaSign])

example :
    (FilterOperator.id (Abstract := Sign)
      (gamma := signConcretizationDomain.gamma)
      (P := fun n : Int => n ≠ 0)) Sign.zero = Sign.zero := by
  rfl

example :
    (RelationalBackwardOperator.id (Abstract := Parity)
      (gamma := parityConcretizationDomain.gamma)
      (rel := fun v₁ v₂ : Int => v₁ + v₂ = 0)) Parity.even Parity.odd =
      (Parity.even, Parity.odd) := by
  rfl

end FrameworkDomainsCapabilities
end Tests
