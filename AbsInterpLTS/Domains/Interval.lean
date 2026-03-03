import Cslib.Init
import Mathlib.Data.Set.Lattice
import AbsInterpLTS.Framework.Domains

namespace AbsInterpLTS
namespace Domains

/--
Baseline interval domain:
`⊥`, bounded interval (`range lo hi`), and `⊤`.
-/
inductive Interval where
  | bot
  | range (lo hi : Int)
  | top
  deriving DecidableEq, Repr

/--
Public smart constructor.
Invalid bounds (`lo > hi`) are normalized to `⊥`.
-/
def mk (lo hi : Int) : Interval :=
  if lo ≤ hi then .range lo hi else .bot

/-- Normalize intervals so invalid ranges collapse to `⊥`. -/
def normalize : Interval -> Interval
  | .bot => .bot
  | .top => .top
  | .range lo hi => mk lo hi

/-- Concretization map from abstract intervals to sets of integers. -/
def gammaInterval : Interval -> Set Int
  | .bot => ∅
  | .range lo hi => { n : Int | lo ≤ n ∧ n ≤ hi }
  | .top => (Set.univ : Set Int)

/-- Domain order induced by concretization inclusion. -/
def leInterval (a b : Interval) : Prop :=
  gammaInterval a ⊆ gammaInterval b

instance : LE Interval where
  le := leInterval

theorem leInterval_refl (a : Interval) : a ≤ a :=
  fun _ hn => hn

theorem leInterval_trans {a b c : Interval} (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c :=
  fun _ hn => hBC (hAB hn)

theorem gammaInterval_monotone_of_leInterval {a b : Interval} (hAB : a ≤ b) :
    gammaInterval a ⊆ gammaInterval b :=
  hAB

/-- `top` concretizes to all integers. -/
theorem gammaInterval_top (n : Int) : n ∈ gammaInterval Interval.top := by
  change True
  trivial

theorem mem_gammaInterval_mk_iff (lo hi n : Int) :
    n ∈ gammaInterval (mk lo hi) ↔ lo ≤ n ∧ n ≤ hi := by
  by_cases h : lo ≤ hi
  · constructor
    · intro hn
      simpa [mk, gammaInterval, h] using hn
    · intro hRange
      simpa [mk, gammaInterval, h] using hRange
  · have hRangeFalse : ¬ (lo ≤ n ∧ n ≤ hi) := by
      intro hRange
      omega
    constructor
    · intro hn
      have : False := by
        simp [mk, gammaInterval, h] at hn
      exact False.elim this
    · intro hRange
      exact False.elim (hRangeFalse hRange)

theorem gammaInterval_mk (lo hi : Int) :
    gammaInterval (mk lo hi) = { n : Int | lo ≤ n ∧ n ≤ hi } := by
  apply Set.ext
  intro n
  simpa using mem_gammaInterval_mk_iff lo hi n

/-- Normalization preserves concretization. -/
theorem gammaInterval_normalize (a : Interval) :
    gammaInterval (normalize a) = gammaInterval a := by
  cases a with
  | bot =>
      rfl
  | top =>
      rfl
  | range lo hi =>
      simpa [normalize, gammaInterval] using gammaInterval_mk lo hi

/-- Join on normalized intervals. -/
def joinInterval (a b : Interval) : Interval :=
  match normalize a, normalize b with
  | .bot, b' => b'
  | a', .bot => a'
  | .top, _ => .top
  | _, .top => .top
  | .range lo1 hi1, .range lo2 hi2 => mk (min lo1 lo2) (max hi1 hi2)

/-- `joinInterval` soundly over-approximates union concretization. -/
theorem joinInterval_sound (a b : Interval) :
    gammaInterval a ∪ gammaInterval b ⊆ gammaInterval (joinInterval a b) := by
  intro n hn
  cases a with
  | bot =>
      have hb : n ∈ gammaInterval b := by
        simpa [gammaInterval] using hn
      have hbNorm : n ∈ gammaInterval (normalize b) := by
        rw [gammaInterval_normalize b]
        exact hb
      simpa [joinInterval, normalize] using hbNorm
  | range lo1 hi1 =>
      cases b with
      | bot =>
          by_cases h1 : lo1 ≤ hi1
          · have hRange : lo1 ≤ n ∧ n ≤ hi1 := by
              simpa [gammaInterval] using hn
            simpa [joinInterval, normalize, mk, h1] using
              (mem_gammaInterval_mk_iff lo1 hi1 n).2 hRange
          · have hRange : lo1 ≤ n ∧ n ≤ hi1 := by
              simpa [gammaInterval] using hn
            have : False := by
              omega
            exact False.elim this
      | range lo2 hi2 =>
          have hRange :
              (lo1 ≤ n ∧ n ≤ hi1) ∨ (lo2 ≤ n ∧ n ≤ hi2) := by
            simpa [gammaInterval] using hn
          by_cases h1 : lo1 ≤ hi1
          · by_cases h2 : lo2 ≤ hi2
            · have hBounds : min lo1 lo2 ≤ n ∧ n ≤ max hi1 hi2 := by
                rcases hRange with hR1 | hR2
                · rcases hR1 with ⟨hLo1, hHi1⟩
                  exact ⟨by omega, by omega⟩
                · rcases hR2 with ⟨hLo2, hHi2⟩
                  exact ⟨by omega, by omega⟩
              simpa [joinInterval, normalize, mk, h1, h2] using
                (mem_gammaInterval_mk_iff (min lo1 lo2) (max hi1 hi2) n).2 hBounds
            · have hR1 : lo1 ≤ n ∧ n ≤ hi1 := by
                rcases hRange with hR1 | hR2
                · exact hR1
                · exfalso
                  rcases hR2 with ⟨hLo2, hHi2⟩
                  omega
              simpa [joinInterval, normalize, mk, h1, h2] using
                (mem_gammaInterval_mk_iff lo1 hi1 n).2 hR1
          · by_cases h2 : lo2 ≤ hi2
            · have hR2 : lo2 ≤ n ∧ n ≤ hi2 := by
                rcases hRange with hR1 | hR2
                · exfalso
                  rcases hR1 with ⟨hLo1, hHi1⟩
                  omega
                · exact hR2
              simpa [joinInterval, normalize, mk, h1, h2] using
                (mem_gammaInterval_mk_iff lo2 hi2 n).2 hR2
            · have : False := by
                rcases hRange with hR1 | hR2
                · rcases hR1 with ⟨hLo1, hHi1⟩
                  omega
                · rcases hR2 with ⟨hLo2, hHi2⟩
                  omega
              exact False.elim this
      | top =>
          by_cases h1 : lo1 ≤ hi1
          · simp [joinInterval, normalize, mk, gammaInterval, h1]
          · simp [joinInterval, normalize, mk, gammaInterval, h1]
  | top =>
      cases b with
      | bot =>
          simp [joinInterval, normalize, gammaInterval]
      | range lo hi =>
          by_cases h : lo ≤ hi
          · simp [joinInterval, normalize, mk, gammaInterval, h]
          · simp [joinInterval, normalize, mk, gammaInterval, h]
      | top =>
          simp [joinInterval, normalize, gammaInterval]

/-- Meet on normalized intervals. -/
def meetInterval (a b : Interval) : Interval :=
  match normalize a, normalize b with
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, b' => b'
  | a', .top => a'
  | .range lo1 hi1, .range lo2 hi2 => mk (max lo1 lo2) (min hi1 hi2)

/-- Baseline unary transfer shape: abstract negation. -/
def negIntervalTransfer (a : Interval) : Interval :=
  match normalize a with
  | .bot => .bot
  | .top => .top
  | .range lo hi => mk (-hi) (-lo)

theorem negIntervalTransfer_sound {a : Interval} {n : Int} (hn : n ∈ gammaInterval a) :
    -n ∈ gammaInterval (negIntervalTransfer a) := by
  cases a with
  | bot =>
      change False at hn
      exact False.elim hn
  | top =>
      change True at hn
      change True
      trivial
  | range lo hi =>
      rcases hn with ⟨hLo, hHi⟩
      have hNorm : lo ≤ hi := by omega
      have hLow : -hi ≤ -n := by omega
      have hHigh : -n ≤ -lo := by omega
      have hMem : -hi ≤ -n ∧ -n ≤ -lo := ⟨hLow, hHigh⟩
      have hMk : mk lo hi = Interval.range lo hi := by
        simp [mk, hNorm]
      simpa [negIntervalTransfer, normalize, hMk] using
        (mem_gammaInterval_mk_iff (-hi) (-lo) (-n)).2 hMem

/-- Gamma-only interface instance for the interval domain. -/
def intervalGammaOnlyDomain :
    AbsInterpLTS.Framework.Domains.GammaOnlyDomain Interval Int where
  gamma := gammaInterval
  le := leInterval
  le_refl := leInterval_refl
  le_trans := leInterval_trans
  gamma_monotone := gammaInterval_monotone_of_leInterval
  top := Interval.top
  gamma_top := gammaInterval_top
  join := joinInterval
  join_sound := joinInterval_sound

end Domains
end AbsInterpLTS
