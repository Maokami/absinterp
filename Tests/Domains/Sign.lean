import Cslib.Init

import AbsInterp

namespace Tests
namespace DomainsSign

open AbsInterp
open AbsInterp.Domains

example : (-3 : Int) ∈ gammaSign Sign.neg := by
  simp [gammaSign]

example : (0 : Int) ∈ gammaSign Sign.zero := by
  simp [gammaSign]

example : (5 : Int) ∈ gammaSign Sign.pos := by
  simp [gammaSign]

example : (4 : Int) ∉ gammaSign Sign.nonpos := by
  simp [gammaSign]

example : Sign.neg ≤ Sign.nonpos := by
  intro n hn
  change n < 0 at hn
  change n < 0 ∨ n = 0
  exact Or.inl hn

example : Sign.zero ≤ Sign.nonneg := by
  intro n hn
  simp [gammaSign] at hn ⊢
  omega

example (a : Sign) : a ≤ a := by
  exact leSign_refl a

example (a b c : Sign) (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c := by
  exact leSign_trans hAB hBC

example : joinSign Sign.neg Sign.zero = Sign.nonpos := by
  rfl

example : joinSign Sign.neg Sign.pos = Sign.top := by
  rfl

example : negTransfer Sign.nonpos = Sign.nonneg := by
  rfl

example (n : Int) (hn : n ∈ gammaSign Sign.nonneg) :
    -n ∈ gammaSign (negTransfer Sign.nonneg) := by
  exact negTransfer_sound hn

-- meetSign tests
example : meetSign Sign.neg Sign.nonneg = Sign.bot := by rfl
example : meetSign Sign.top Sign.pos = Sign.pos := by rfl
example : meetSign Sign.nonpos Sign.nonneg = Sign.zero := by rfl
example : meetSign Sign.neg Sign.nonpos = Sign.neg := by rfl

-- assumeNonzeroAddSign tests
/-- nonneg + zero ≠ 0 refines nonneg to pos. -/
example : (assumeNonzeroAddSign Sign.nonneg Sign.zero).1 = Sign.pos := by rfl
/-- zero + top ≠ 0 refines top to top (nonzero). -/
example : (assumeNonzeroAddSign Sign.zero Sign.top).2 = Sign.top := by rfl

-- assumeZeroAddSign tests
/-- top + pos = 0 refines top to neg. -/
example : (assumeZeroAddSign Sign.top Sign.pos).1 = Sign.neg := by rfl
/-- pos + top = 0 refines top to neg. -/
example : (assumeZeroAddSign Sign.pos Sign.top).2 = Sign.neg := by rfl
/-- nonneg + zero = 0 refines nonneg to zero. -/
example : (assumeZeroAddSign Sign.nonneg Sign.zero).1 = Sign.zero := by rfl
/-- top + nonneg = 0 refines top to nonpos. -/
example : (assumeZeroAddSign Sign.top Sign.nonneg).1 = Sign.nonpos := by rfl

open AbsInterp.Framework

/-- The identity abstract transformer is monotone over Sign. -/
example : MonotonePostSharp (id : Sign → Sign) :=
  MonotonePostSharp.id

end DomainsSign
end Tests
