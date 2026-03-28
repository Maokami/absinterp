import Cslib.Init

import AbsInterp

namespace Tests
namespace DomainsInterval

open AbsInterp
open AbsInterp.Domains

example : (2 : Int) ∈ gammaInterval (mk 1 3) := by
  simp [gammaInterval, mk]

example : (4 : Int) ∉ gammaInterval (mk 1 3) := by
  simp [gammaInterval, mk]

example : mk 3 1 = Interval.bot := by
  simp [mk]

example : normalize (Interval.range 3 1) = Interval.bot := by
  simp [normalize, mk]

example : (0 : Int) ∈ gammaInterval Interval.top := by
  simp [gammaInterval]

example : Interval.range 1 2 ≤ Interval.range 0 3 := by
  intro n hn
  rcases hn with ⟨hLo, hHi⟩
  exact ⟨by omega, by omega⟩

example (a : Interval) : a ≤ a := by
  exact leInterval_refl a

example (a b c : Interval) (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c := by
  exact leInterval_trans hAB hBC

example (lo hi n : Int) :
    n ∈ gammaInterval (mk lo hi) ↔ lo ≤ n ∧ n ≤ hi := by
  simpa using mem_gammaInterval_mk_iff lo hi n

example : joinInterval (mk 1 2) (mk 4 5) = mk 1 5 := by
  simp [joinInterval, normalize, mk]

example : joinInterval (Interval.range 3 1) (mk 0 0) = mk 0 0 := by
  simp [joinInterval, normalize, mk]

example : meetInterval (mk 1 4) (mk 3 6) = mk 3 4 := by
  simp [meetInterval, normalize, mk]

example : meetInterval (mk 1 2) (mk 4 5) = Interval.bot := by
  simp [meetInterval, normalize, mk]

example (n : Int) (hn : n ∈ gammaInterval (meetInterval (mk 1 4) (mk 3 6))) :
    n ∈ gammaInterval (mk 1 4) ∩ gammaInterval (mk 3 6) := by
  exact meetInterval_sound (a := mk 1 4) (b := mk 3 6) hn

example : negIntervalTransfer (mk 1 4) = mk (-4) (-1) := by
  simp [negIntervalTransfer, normalize, mk]

example (n : Int) (hn : n ∈ gammaInterval (mk (-2) 5)) :
    -n ∈ gammaInterval (negIntervalTransfer (mk (-2) 5)) := by
  exact negIntervalTransfer_sound hn

end DomainsInterval
end Tests
