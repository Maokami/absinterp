import Cslib.Init

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
      have : n ∈ (∅ : Set Int) := by
        simpa [mk, gammaInterval, h] using hn
      have : False := by
        simpa using this
      exact False.elim this
    · intro hRange
      exact False.elim (hRangeFalse hRange)

theorem gammaInterval_mk (lo hi : Int) :
    gammaInterval (mk lo hi) = { n : Int | lo ≤ n ∧ n ≤ hi } := by
  apply Set.ext
  intro n
  simpa using mem_gammaInterval_mk_iff lo hi n

/-- Join on normalized intervals. -/
def joinInterval (a b : Interval) : Interval :=
  match normalize a, normalize b with
  | .bot, b' => b'
  | a', .bot => a'
  | .top, _ => .top
  | _, .top => .top
  | .range lo1 hi1, .range lo2 hi2 => mk (min lo1 lo2) (max hi1 hi2)

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
      have hNegNorm : -hi ≤ -lo := by omega
      have hLow : -hi ≤ -n := by omega
      have hHigh : -n ≤ -lo := by omega
      simp [negIntervalTransfer, normalize, mk, hNorm, hNegNorm, gammaInterval]
      exact ⟨hLow, hHigh⟩

end Domains
end AbsInterpLTS
