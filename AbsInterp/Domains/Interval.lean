import Cslib.Init
import AbsInterp.Framework.Domains.Gamma
import AbsInterp.Framework.Iteration.Widening.Defs

namespace AbsInterp
namespace Domains

/--
Baseline interval domain:
`⊥`, canonical bounded interval (`range lo hi h` where `h : lo ≤ hi`), and `⊤`.

The proof field `h` makes the representation canonical: `range lo hi` is only
constructible when `lo ≤ hi`, so `Interval.range 3 1` is impossible.
-/
inductive Interval where
  | bot
  | range (lo hi : Int) (h : lo ≤ hi)
  | top
  deriving DecidableEq

instance : Bot Interval where
  bot := .bot

instance : Repr Interval where
  reprPrec a _ := match a with
    | .bot => "⊥"
    | .range lo hi _ => "[" ++ reprPrec lo 0 ++ ", " ++ reprPrec hi 0 ++ "]"
    | .top => "⊤"

/--
Public smart constructor: `mk lo hi = range lo hi h` when `lo ≤ hi` (with `h` the proof),
and `mk lo hi = ⊥` otherwise.
-/
def mk (lo hi : Int) : Interval :=
  if h : lo ≤ hi then .range lo hi h else .bot

/-- Concretization map from abstract intervals to sets of integers. -/
def gammaInterval : Interval → Set Int
  | .bot => ∅
  | .range lo hi _ => { n : Int | lo ≤ n ∧ n ≤ hi }
  | .top => Set.univ

/-- Domain order induced by concretization inclusion. -/
def leInterval (a b : Interval) : Prop :=
  gammaInterval a ⊆ gammaInterval b

theorem leInterval_refl (a : Interval) : leInterval a a :=
  fun _ hn => hn

theorem leInterval_trans {a b c : Interval} (hAB : leInterval a b) (hBC : leInterval b c) :
    leInterval a c :=
  fun _ hn => hBC (hAB hn)

theorem leInterval_antisymm {a b : Interval} (hab : leInterval a b) (hba : leInterval b a) :
    a = b := by
  cases a with
  | bot =>
    cases b with
    | bot => rfl
    | range lo hi h =>
      have hmem : lo ∈ gammaInterval (Interval.range lo hi h) := ⟨le_refl lo, h⟩
      have := hba hmem
      simp only [gammaInterval, Set.mem_empty_iff_false] at this
    | top =>
      have hmem : (0 : Int) ∈ gammaInterval Interval.top := Set.mem_univ 0
      have := hba hmem
      simp only [gammaInterval, Set.mem_empty_iff_false] at this
  | range lo1 hi1 h1 =>
    cases b with
    | bot =>
      have hmem : lo1 ∈ gammaInterval (Interval.range lo1 hi1 h1) := ⟨le_refl lo1, h1⟩
      have := hab hmem
      simp only [gammaInterval, Set.mem_empty_iff_false] at this
    | range lo2 hi2 h2 =>
      have hlo1_in_b : lo1 ∈ gammaInterval (Interval.range lo2 hi2 h2) :=
        hab ⟨le_refl lo1, h1⟩
      have hlo2_in_a : lo2 ∈ gammaInterval (Interval.range lo1 hi1 h1) :=
        hba ⟨le_refl lo2, h2⟩
      have hhi1_in_b : hi1 ∈ gammaInterval (Interval.range lo2 hi2 h2) :=
        hab ⟨h1, le_refl hi1⟩
      have hhi2_in_a : hi2 ∈ gammaInterval (Interval.range lo1 hi1 h1) :=
        hba ⟨h2, le_refl hi2⟩
      simp only [gammaInterval, Set.mem_setOf_eq] at hlo1_in_b hlo2_in_a hhi1_in_b hhi2_in_a
      have hloEq : lo1 = lo2 := le_antisymm hlo2_in_a.1 hlo1_in_b.1
      have hhiEq : hi1 = hi2 := le_antisymm hhi1_in_b.2 hhi2_in_a.2
      subst hloEq; subst hhiEq
      congr 1
    | top =>
      have hcontra : hi1 + 1 ∈ gammaInterval (Interval.range lo1 hi1 h1) :=
        hba (Set.mem_univ _)
      simp only [gammaInterval, Set.mem_setOf_eq] at hcontra
      omega
  | top =>
    cases b with
    | bot =>
      have hmem : (0 : Int) ∈ gammaInterval Interval.top := Set.mem_univ 0
      have := hab hmem
      simp only [gammaInterval, Set.mem_empty_iff_false] at this
    | range lo2 hi2 h2 =>
      have hcontra : hi2 + 1 ∈ gammaInterval (Interval.range lo2 hi2 h2) :=
        hab (Set.mem_univ _)
      simp only [gammaInterval, Set.mem_setOf_eq] at hcontra
      omega
    | top => rfl

instance : PartialOrder Interval where
  le := leInterval
  le_refl := leInterval_refl
  le_trans := @leInterval_trans
  le_antisymm := fun _ _ => leInterval_antisymm

instance : OrderTop Interval where
  top := .top
  le_top _ := Set.subset_univ _

theorem gammaInterval_monotone_of_leInterval {a b : Interval} (hAB : a ≤ b) :
    gammaInterval a ⊆ gammaInterval b :=
  hAB

/-- `top` concretizes to all integers. -/
theorem gammaInterval_top (n : Int) : n ∈ gammaInterval Interval.top :=
  Set.mem_univ n

theorem mem_gammaInterval_mk_iff (lo hi n : Int) :
    n ∈ gammaInterval (mk lo hi) ↔ lo ≤ n ∧ n ≤ hi := by
  simp only [mk]
  split
  · next h => simp only [gammaInterval, Set.mem_setOf_eq]
  · next h =>
    constructor
    · intro hn; simp only [gammaInterval, Set.mem_empty_iff_false] at hn
    · intro ⟨hlo, hhi⟩; exact absurd (le_trans hlo hhi) h

theorem gammaInterval_mk (lo hi : Int) :
    gammaInterval (mk lo hi) = { n : Int | lo ≤ n ∧ n ≤ hi } := by
  ext n
  exact mem_gammaInterval_mk_iff lo hi n

/-- Join of two canonical intervals. -/
def joinInterval (a b : Interval) : Interval :=
  match a, b with
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .range lo1 hi1 h1, .range lo2 hi2 h2 =>
      .range (min lo1 lo2) (max hi1 hi2) (by omega)

instance : Max Interval := ⟨joinInterval⟩

theorem joinInterval_le_left (a b : Interval) : leInterval a (joinInterval a b) := by
  intro n hn
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    cases b with
    | bot => simp only [joinInterval]; exact hn
    | top => simp only [joinInterval]; exact hn
    | range _ _ _ => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
  | range lo1 hi1 h1 =>
    cases b with
    | bot => simp only [joinInterval]; exact hn
    | top => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
    | range lo2 hi2 h2 =>
      simp only [gammaInterval, Set.mem_setOf_eq] at hn
      simp only [joinInterval, gammaInterval, Set.mem_setOf_eq]
      omega

theorem joinInterval_le_right (a b : Interval) : leInterval b (joinInterval a b) := by
  intro n hn
  cases b with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    cases a with
    | bot => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
    | top => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
    | range _ _ _ => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
  | range lo2 hi2 h2 =>
    cases a with
    | bot => simp only [joinInterval]; exact hn
    | top => simp only [joinInterval, gammaInterval]; exact Set.mem_univ n
    | range lo1 hi1 h1 =>
      simp only [gammaInterval, Set.mem_setOf_eq] at hn
      simp only [joinInterval, gammaInterval, Set.mem_setOf_eq]
      omega

theorem joinInterval_le_of_le {a b c : Interval} (ha : leInterval a c) (hb : leInterval b c) :
    leInterval (joinInterval a b) c := by
  intro n hn
  cases a with
  | bot =>
    simp only [joinInterval] at hn
    exact hb hn
  | top =>
    cases b with
    | bot =>
      simp only [joinInterval] at hn
      exact ha hn
    | top =>
      simp only [joinInterval] at hn
      exact ha hn
    | range _ _ _ =>
      simp only [joinInterval] at hn
      exact ha hn
  | range lo1 hi1 h1 =>
    cases b with
    | bot =>
      simp only [joinInterval] at hn
      exact ha hn
    | top =>
      simp only [joinInterval] at hn
      exact hb hn
    | range lo2 hi2 h2 =>
      simp only [joinInterval, gammaInterval, Set.mem_setOf_eq] at hn
      cases c with
      | bot =>
        have := ha ⟨le_refl lo1, h1⟩
        simp only [gammaInterval, Set.mem_empty_iff_false] at this
      | top => exact Set.mem_univ n
      | range lo3 hi3 h3 =>
        simp only [gammaInterval, Set.mem_setOf_eq]
        have hlo1 := ha ⟨le_refl lo1, h1⟩
        have hhi1 := ha ⟨h1, le_refl hi1⟩
        have hlo2 := hb ⟨le_refl lo2, h2⟩
        have hhi2 := hb ⟨h2, le_refl hi2⟩
        simp only [gammaInterval, Set.mem_setOf_eq] at hlo1 hhi1 hlo2 hhi2
        omega

instance : SemilatticeSup Interval where
  sup := joinInterval
  le_sup_left := joinInterval_le_left
  le_sup_right := joinInterval_le_right
  sup_le _ _ _ ha hb := joinInterval_le_of_le ha hb

/-- `joinInterval` soundly over-approximates union concretization. -/
theorem joinInterval_sound (a b : Interval) :
    gammaInterval a ∪ gammaInterval b ⊆ gammaInterval (joinInterval a b) := by
  intro n hn
  rcases hn with ha | hb
  · exact joinInterval_le_left a b ha
  · exact joinInterval_le_right a b hb

/-- Meet of two canonical intervals. -/
def meetInterval (a b : Interval) : Interval :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, b => b
  | a, .top => a
  | .range lo1 hi1 _, .range lo2 hi2 _ => mk (max lo1 lo2) (min hi1 hi2)

/-- `meetInterval` soundly under-approximates intersection concretization. -/
theorem meetInterval_sound (a b : Interval) :
    gammaInterval (meetInterval a b) ⊆ gammaInterval a ∩ gammaInterval b := by
  intro n hn
  cases a with
  | bot => simp only [meetInterval, gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    cases b with
    | bot => simp only [meetInterval, gammaInterval, Set.mem_empty_iff_false] at hn
    | top =>
      simp only [gammaInterval, Set.mem_inter_iff, Set.mem_univ, and_self]
    | range lo hi h =>
      simp only [meetInterval] at hn
      exact ⟨Set.mem_univ n, hn⟩
  | range lo1 hi1 h1 =>
    cases b with
    | bot => simp only [meetInterval, gammaInterval, Set.mem_empty_iff_false] at hn
    | top =>
      simp only [meetInterval] at hn
      exact ⟨hn, Set.mem_univ n⟩
    | range lo2 hi2 h2 =>
      simp only [meetInterval] at hn
      have hBounds := (mem_gammaInterval_mk_iff (max lo1 lo2) (min hi1 hi2) n).1 hn
      simp only [gammaInterval, Set.mem_inter_iff, Set.mem_setOf_eq]
      omega

/-- Abstract negation on canonical intervals. -/
def negIntervalTransfer (a : Interval) : Interval :=
  match a with
  | .bot => .bot
  | .top => .top
  | .range lo hi h => .range (-hi) (-lo) (by omega)

theorem negIntervalTransfer_sound {a : Interval} {n : Int} (hn : n ∈ gammaInterval a) :
    -n ∈ gammaInterval (negIntervalTransfer a) := by
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top => exact Set.mem_univ _
  | range lo hi h =>
    simp only [gammaInterval, Set.mem_setOf_eq] at hn
    simp only [negIntervalTransfer, gammaInterval, Set.mem_setOf_eq]
    omega

/-- Exact interval for an integer literal. -/
def constInterval (n : Int) : Interval :=
  mk n n

/-- `constInterval` contains the concrete integer it abstracts. -/
theorem constInterval_sound (n : Int) :
    n ∈ gammaInterval (constInterval n) :=
  (mem_gammaInterval_mk_iff n n n).2 ⟨le_rfl, le_rfl⟩

/--
Sound abstract addition on intervals.

For bounded intervals, the result bounds are the sums of the input bounds.
-/
def addIntervalTransfer (a b : Interval) : Interval :=
  match a, b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, _ => .top
  | _, .top => .top
  | .range lo1 hi1 h1, .range lo2 hi2 h2 => .range (lo1 + lo2) (hi1 + hi2) (by omega)

/-- `addIntervalTransfer` soundly abstracts integer addition. -/
theorem addIntervalTransfer_sound
    {a b : Interval} {m n : Int}
    (hm : m ∈ gammaInterval a)
    (hn : n ∈ gammaInterval b) :
    m + n ∈ gammaInterval (addIntervalTransfer a b) := by
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hm
  | top =>
    cases b with
    | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
    | top => exact Set.mem_univ _
    | range lo2 hi2 h2 => exact Set.mem_univ _
  | range lo1 hi1 h1 =>
    cases b with
    | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
    | top => exact Set.mem_univ _
    | range lo2 hi2 h2 =>
      simp only [gammaInterval, Set.mem_setOf_eq] at hm hn
      simp only [addIntervalTransfer, gammaInterval, Set.mem_setOf_eq]
      omega

/-- Refine an interval by assuming the concrete value is nonzero.

For intervals straddling zero, this returns the original interval since
intervals are convex and cannot represent the gap. Precision is lost but
soundness is preserved.
-/
def assumeNonzeroInterval (a : Interval) : Interval :=
  match a with
  | .bot => .bot
  | .top => .top
  | .range lo hi h =>
      if hi < 0 then .range lo hi h
      else if 0 < lo then .range lo hi h
      else if lo = 0 ∧ hi = 0 then .bot
      else if lo = 0 then mk 1 hi
      else if hi = 0 then mk lo (-1)
      else .range lo hi h

/-- `assumeNonzeroInterval` is sound for a concrete witness known to be nonzero. -/
theorem assumeNonzeroInterval_sound
    {a : Interval} {n : Int}
    (hn : n ∈ gammaInterval a)
    (hNe : n ≠ 0) :
    n ∈ gammaInterval (assumeNonzeroInterval a) := by
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top => exact Set.mem_univ _
  | range lo hi h =>
    simp only [gammaInterval, Set.mem_setOf_eq] at hn
    rcases hn with ⟨hLo, hHi⟩
    simp only [assumeNonzeroInterval]
    split
    · simp only [gammaInterval, Set.mem_setOf_eq]; exact ⟨hLo, hHi⟩
    · split
      · simp only [gammaInterval, Set.mem_setOf_eq]; exact ⟨hLo, hHi⟩
      · split
        · rename_i _ _ hBoth
          rcases hBoth with ⟨hlo0, hhi0⟩; omega
        · split
          · exact (mem_gammaInterval_mk_iff 1 hi n).2 ⟨by omega, hHi⟩
          · split
            · exact (mem_gammaInterval_mk_iff lo (-1) n).2 ⟨hLo, by omega⟩
            · simp only [gammaInterval, Set.mem_setOf_eq]; exact ⟨hLo, hHi⟩

/-- Refine an interval by assuming the concrete value is exactly zero. -/
def assumeZeroInterval (a : Interval) : Interval :=
  match a with
  | .bot => .bot
  | .top => mk 0 0
  | .range lo hi _ =>
      if lo ≤ 0 ∧ 0 ≤ hi then mk 0 0 else .bot

/-- `assumeZeroInterval` is sound for a concrete witness known to be zero. -/
theorem assumeZeroInterval_sound
    {a : Interval} {n : Int}
    (hn : n ∈ gammaInterval a)
    (hZero : n = 0) :
    n ∈ gammaInterval (assumeZeroInterval a) := by
  subst hZero
  cases a with
  | bot => simp only [gammaInterval, Set.mem_empty_iff_false] at hn
  | top =>
    simp only [assumeZeroInterval]
    exact (mem_gammaInterval_mk_iff 0 0 0).2 ⟨le_rfl, le_rfl⟩
  | range lo hi _ =>
    simp only [gammaInterval, Set.mem_setOf_eq] at hn
    simp only [assumeZeroInterval]
    split
    · exact (mem_gammaInterval_mk_iff 0 0 0).2 ⟨le_rfl, le_rfl⟩
    · rename_i hNot
      push Not at hNot
      omega

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

/-- Gamma-only interface instance for the interval domain. -/
def intervalGammaDomain :
    AbsInterp.Framework.Domains.GammaDomain Interval Int where
  gamma := gammaInterval
  gamma_monotone := gammaInterval_monotone_of_leInterval
  gamma_top := gammaInterval_top
  join_sound := joinInterval_sound

end Domains
end AbsInterp
