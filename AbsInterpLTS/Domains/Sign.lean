import Cslib.Init

namespace AbsInterpLTS
namespace Domains

/--
Seven-point sign domain:
`⊥`, singletons (`neg`, `zero`, `pos`), pair-wise joins (`nonpos`, `nonneg`), and `⊤`.
-/
inductive Sign where
  | bot
  | neg
  | zero
  | pos
  | nonpos
  | nonneg
  | top
  deriving DecidableEq, Repr

/-- Concretization map from abstract signs to sets of integers. -/
def gammaSign : Sign -> Set Int
  | .bot => ∅
  | .neg => { n : Int | n < 0 }
  | .zero => { n : Int | n = 0 }
  | .pos => { n : Int | 0 < n }
  | .nonpos => { n : Int | n < 0 ∨ n = 0 }
  | .nonneg => { n : Int | n = 0 ∨ 0 < n }
  | .top => (Set.univ : Set Int)

/-- Domain order induced by concretization inclusion. -/
def leSign (a b : Sign) : Prop :=
  gammaSign a ⊆ gammaSign b

instance : LE Sign where
  le := leSign

theorem leSign_refl (a : Sign) : a ≤ a :=
  fun _ hn => hn

theorem leSign_trans {a b c : Sign} (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c :=
  fun _ hn => hBC (hAB hn)

theorem gammaSign_monotone_of_leSign {a b : Sign} (hAB : a ≤ b) :
    gammaSign a ⊆ gammaSign b :=
  hAB

private def hasNeg : Sign -> Bool
  | .bot => false
  | .neg => true
  | .zero => false
  | .pos => false
  | .nonpos => true
  | .nonneg => false
  | .top => true

private def hasZero : Sign -> Bool
  | .bot => false
  | .neg => false
  | .zero => true
  | .pos => false
  | .nonpos => true
  | .nonneg => true
  | .top => true

private def hasPos : Sign -> Bool
  | .bot => false
  | .neg => false
  | .zero => false
  | .pos => true
  | .nonpos => false
  | .nonneg => true
  | .top => true

private def signOfFlags (neg zero pos : Bool) : Sign :=
  match neg, zero, pos with
  | false, false, false => .bot
  | true, false, false => .neg
  | false, true, false => .zero
  | false, false, true => .pos
  | true, true, false => .nonpos
  | false, true, true => .nonneg
  | true, false, true => .top
  | true, true, true => .top

/-- Join on signs, with `{neg,pos}` normalized to `top`. -/
def joinSign (a b : Sign) : Sign :=
  signOfFlags
    (hasNeg a || hasNeg b)
    (hasZero a || hasZero b)
    (hasPos a || hasPos b)

/-- Baseline unary transfer shape: abstract negation. -/
def negTransfer : Sign -> Sign
  | .bot => .bot
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg
  | .nonpos => .nonneg
  | .nonneg => .nonpos
  | .top => .top

theorem negTransfer_sound {a : Sign} {n : Int} (hn : n ∈ gammaSign a) :
    -n ∈ gammaSign (negTransfer a) := by
  cases a with
  | bot =>
      change False at hn
      exact False.elim hn
  | neg =>
      change n < 0 at hn
      change 0 < -n
      omega
  | zero =>
      change n = 0 at hn
      change -n = 0
      omega
  | pos =>
      change 0 < n at hn
      change -n < 0
      omega
  | nonpos =>
      change n < 0 ∨ n = 0 at hn
      change -n = 0 ∨ 0 < -n
      omega
  | nonneg =>
      change n = 0 ∨ 0 < n at hn
      change -n < 0 ∨ -n = 0
      omega
  | top =>
      change True at hn
      change True
      trivial

end Domains
end AbsInterpLTS
