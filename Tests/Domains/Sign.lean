import Cslib.Init

import AbsInterpLTS

namespace Tests
namespace DomainsSign

open AbsInterpLTS
open AbsInterpLTS.Domains

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

open AbsInterpLTS.Framework

/-- The identity abstract transformer is monotone over Sign. -/
example : MonotonePostSharp (fun a : Sign => a) :=
  MonotonePostSharp.id

end DomainsSign
end Tests
