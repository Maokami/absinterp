import AbsInterp.Domains.Interval
import AbsInterp.Framework.Iteration.Widening.Defs

/-!
# Interval widening

Widening operator and upper-bound lemmas for the baseline interval domain.
Lives in the iteration/solver layer so that `AbsInterp.Domains.Interval`
remains free of framework iteration dependencies.
-/

namespace AbsInterp
namespace Domains

/--
Widening on intervals: if the new interval `b` exceeds `a`'s bounds in
either direction, jump to `⊤`. This aggressive strategy guarantees
termination in at most one widening step.
-/
def widenInterval (a b : Interval) : Interval :=
  match a, b with
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .range lo1 hi1 h1, .range lo2 hi2 _ =>
      if lo2 < lo1 ∨ hi1 < hi2 then .top else .range lo1 hi1 h1

/-- `widenInterval` is an upper bound: `a ≤ widen a b`. -/
theorem widenInterval_left (a b : Interval) :
    leInterval a (widenInterval a b) := by
  intro n hn
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    cases b with
    | bot => simp only [widenInterval]; exact hn
    | top => simp only [widenInterval]; exact hn
    | range _ _ _ => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
  | range lo1 hi1 h1 =>
    cases b with
    | bot => simp only [widenInterval]; exact hn
    | top => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
    | range lo2 hi2 _ =>
      simp only [widenInterval]
      split_ifs with hcond
      · exact Set.mem_univ n
      · exact hn

/-- `widenInterval` is an upper bound: `b ≤ widen a b`. -/
theorem widenInterval_right (a b : Interval) :
    leInterval b (widenInterval a b) := by
  intro n hn
  cases b with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    cases a with
    | bot => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
    | top => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
    | range _ _ _ => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
  | range lo2 hi2 h2 =>
    cases a with
    | bot => simp only [widenInterval]; exact hn
    | top => simp only [widenInterval, gammaInterval]; exact Set.mem_univ n
    | range lo1 hi1 h1 =>
      simp only [widenInterval]
      split_ifs with hcond
      · exact Set.mem_univ n
      · push Not at hcond
        simp only [gammaInterval, Set.mem_setOf_eq] at hn ⊢
        omega

/-- `widenInterval` satisfies the framework `WidenUpperBound` contract. -/
theorem widenInterval_upperBound :
    AbsInterp.Framework.Iteration.WidenUpperBound leInterval widenInterval where
  left := widenInterval_left
  right := widenInterval_right

end Domains
end AbsInterp
