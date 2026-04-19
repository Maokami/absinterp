import Cslib.Init
import AbsInterp.Framework.Domains.Gamma

namespace AbsInterp
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

instance : Bot Sign where
  bot := .bot

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

theorem leSign_refl (a : Sign) : leSign a a :=
  fun _ hn => hn

theorem leSign_trans {a b c : Sign} (hAB : leSign a b) (hBC : leSign b c) : leSign a c :=
  fun _ hn => hBC (hAB hn)

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

/-- If `γ(a) ⊆ γ(b)` and `a` has a negative witness, so does `b`. -/
private theorem hasNeg_of_leSign {a b : Sign} (h : leSign a b) (hN : hasNeg a = true) :
    hasNeg b = true := by
  have hMem : (-1 : Int) ∈ gammaSign a := by
    cases a <;> simp_all [hasNeg, gammaSign]
  have hMemB := h hMem
  cases b <;> simp_all [hasNeg, gammaSign]

/-- If `γ(a) ⊆ γ(b)` and `a` has a zero witness, so does `b`. -/
private theorem hasZero_of_leSign {a b : Sign} (h : leSign a b) (hZ : hasZero a = true) :
    hasZero b = true := by
  have hMem : (0 : Int) ∈ gammaSign a := by
    cases a <;> simp_all [hasZero, gammaSign]
  have hMemB := h hMem
  cases b <;> simp_all [hasZero, gammaSign]

/-- If `γ(a) ⊆ γ(b)` and `a` has a positive witness, so does `b`. -/
private theorem hasPos_of_leSign {a b : Sign} (h : leSign a b) (hP : hasPos a = true) :
    hasPos b = true := by
  have hMem : (1 : Int) ∈ gammaSign a := by
    cases a <;> simp_all [hasPos, gammaSign]
  have hMemB := h hMem
  cases b <;> simp_all [hasPos, gammaSign]

theorem leSign_antisymm {a b : Sign} (hab : leSign a b) (hba : leSign b a) : a = b := by
  have hN1 := hasNeg_of_leSign hab
  have hN2 := hasNeg_of_leSign hba
  have hZ1 := hasZero_of_leSign hab
  have hZ2 := hasZero_of_leSign hba
  have hP1 := hasPos_of_leSign hab
  have hP2 := hasPos_of_leSign hba
  cases a <;> cases b <;>
    first
    | rfl
    | (exfalso; simp_all [hasNeg, hasZero, hasPos])

instance : PartialOrder Sign where
  le := leSign
  le_refl := leSign_refl
  le_trans := @leSign_trans
  le_antisymm := fun _ _ => leSign_antisymm

instance : OrderTop Sign where
  top := .top
  le_top _ := Set.subset_univ _

theorem gammaSign_monotone_of_leSign {a b : Sign} (hAB : a ≤ b) :
    gammaSign a ⊆ gammaSign b :=
  hAB

/-- `top` concretizes to all integers. -/
theorem gammaSign_top (n : Int) : n ∈ gammaSign Sign.top := by
  change True
  trivial

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

instance : Max Sign := ⟨joinSign⟩

/-- `joinSign` soundly over-approximates union concretization. -/
theorem joinSign_sound (a b : Sign) :
    gammaSign a ∪ gammaSign b ⊆ gammaSign (a ⊔ b) := by
  intro n hn
  show n ∈ gammaSign (joinSign a b)
  cases a <;> cases b <;>
    simp [gammaSign, joinSign, signOfFlags, hasNeg, hasZero, hasPos] at hn ⊢ <;>
    tauto

@[simp] theorem joinSign_bot_left (a : Sign) :
    joinSign .bot a = a := by
  cases a <;> rfl

@[simp] theorem joinSign_bot_right (a : Sign) :
    joinSign a .bot = a := by
  cases a <;> rfl

theorem joinSign_le_left (a b : Sign) : a ≤ joinSign a b :=
  fun _ hn => joinSign_sound a b (Or.inl hn)

theorem joinSign_le_right (a b : Sign) : b ≤ joinSign a b :=
  fun _ hn => joinSign_sound a b (Or.inr hn)

theorem joinSign_le_of_le {a b c : Sign} (ha : a ≤ c) (hb : b ≤ c) :
    joinSign a b ≤ c := by
  have hN_ac := hasNeg_of_leSign ha
  have hN_bc := hasNeg_of_leSign hb
  have hZ_ac := hasZero_of_leSign ha
  have hZ_bc := hasZero_of_leSign hb
  have hP_ac := hasPos_of_leSign ha
  have hP_bc := hasPos_of_leSign hb
  intro n hn
  cases a <;> cases b <;> cases c <;>
    simp_all [gammaSign, joinSign, signOfFlags, hasNeg, hasZero, hasPos]

instance : SemilatticeSup Sign where
  sup := joinSign
  le_sup_left := joinSign_le_left
  le_sup_right := joinSign_le_right
  sup_le _ _ _ ha hb := joinSign_le_of_le ha hb

/-- Exact sign for an integer literal. -/
def constSign (n : Int) : Sign :=
  if n < 0 then .neg else if n = 0 then .zero else .pos

/-- `constSign` contains the concrete integer it abstracts. -/
theorem constSign_sound (n : Int) :
    n ∈ gammaSign (constSign n) := by
  by_cases hNeg : n < 0
  · simp [constSign, gammaSign, hNeg]
  · by_cases hZero : n = 0
    · simp [constSign, gammaSign, hZero]
    · have hPos : 0 < n := by omega
      simp [constSign, gammaSign, hNeg, hZero, hPos]

/--
Sound abstract addition on signs.

This is intentionally lightweight: it aims for a useful, sound
over-approximation rather than maximal precision.
-/
def addTransfer : Sign -> Sign -> Sign
  | .bot, _ => .bot
  | _, .bot => .bot
  | .zero, b => b
  | a, .zero => a
  | .neg, .neg => .neg
  | .neg, .nonpos => .neg
  | .neg, .pos => .top
  | .neg, .nonneg => .top
  | .neg, .top => .top
  | .pos, .neg => .top
  | .pos, .pos => .pos
  | .pos, .nonpos => .top
  | .pos, .nonneg => .pos
  | .pos, .top => .top
  | .nonpos, .neg => .neg
  | .nonpos, .pos => .top
  | .nonpos, .nonpos => .nonpos
  | .nonpos, .nonneg => .top
  | .nonpos, .top => .top
  | .nonneg, .neg => .top
  | .nonneg, .pos => .pos
  | .nonneg, .nonpos => .top
  | .nonneg, .nonneg => .nonneg
  | .nonneg, .top => .top
  | .top, .neg => .top
  | .top, .pos => .top
  | .top, .nonpos => .top
  | .top, .nonneg => .top
  | .top, .top => .top

/-- `addTransfer` soundly abstracts integer addition. -/
theorem addTransfer_sound
    {a b : Sign}
    {m n : Int}
    (hm : m ∈ gammaSign a)
    (hn : n ∈ gammaSign b) :
    m + n ∈ gammaSign (addTransfer a b) := by
  cases a <;> cases b <;>
    simp [gammaSign, addTransfer] at hm hn ⊢ <;>
    omega

/-- Refine a sign by assuming the concrete value is nonzero. -/
def assumeNonzero : Sign -> Sign
  | .bot => .bot
  | .neg => .neg
  | .zero => .bot
  | .pos => .pos
  | .nonpos => .neg
  | .nonneg => .pos
  | .top => .top

/-- Refine a sign by assuming the concrete value is exactly zero. -/
def assumeZero : Sign -> Sign
  | .bot => .bot
  | .neg => .bot
  | .zero => .zero
  | .pos => .bot
  | .nonpos => .zero
  | .nonneg => .zero
  | .top => .zero

/-- `assumeNonzero` is sound for a concrete witness known to be nonzero. -/
theorem assumeNonzero_sound
    {a : Sign}
    {n : Int}
    (hn : n ∈ gammaSign a)
    (hNe : n ≠ 0) :
    n ∈ gammaSign (assumeNonzero a) := by
  cases a <;>
    simp [gammaSign, assumeNonzero] at hn ⊢ <;>
    omega

/-- `assumeZero` is sound for a concrete witness known to be zero. -/
theorem assumeZero_sound
    {a : Sign}
    {n : Int}
    (hn : n ∈ gammaSign a)
    (hZero : n = 0) :
    n ∈ gammaSign (assumeZero a) := by
  cases a <;>
    simp [gammaSign, assumeZero] at hn ⊢ <;>
    omega

/-- Meet (greatest lower bound) on signs. -/
def meetSign (a b : Sign) : Sign :=
  signOfFlags
    (hasNeg a && hasNeg b)
    (hasZero a && hasZero b)
    (hasPos a && hasPos b)

/-- `meetSign` is sound: intersection of concretizations is contained in the meet. -/
theorem meetSign_sound
    {a b : Sign}
    {n : Int}
    (ha : n ∈ gammaSign a)
    (hb : n ∈ gammaSign b) :
    n ∈ gammaSign (meetSign a b) := by
  cases a <;> cases b <;>
    simp [gammaSign, meetSign, signOfFlags, hasNeg, hasZero, hasPos] at ha hb ⊢ <;>
    omega

/-- Backward refinement for addition under nonzero constraint. -/
def assumeNonzeroAddSign (a₁ a₂ : Sign) : Sign × Sign :=
  if a₁ = .bot ∨ a₂ = .bot then (.bot, .bot)
  else match a₂ with
  | .zero => (assumeNonzero a₁, a₂)
  | _ => match a₁ with
    | .zero => (a₁, assumeNonzero a₂)
    | _ => (a₁, a₂)

/-- `assumeNonzeroAddSign` is sound. -/
theorem assumeNonzeroAddSign_sound
    {a₁ a₂ : Sign}
    {v₁ v₂ : Int}
    (h₁ : v₁ ∈ gammaSign a₁)
    (h₂ : v₂ ∈ gammaSign a₂)
    (hNe : v₁ + v₂ ≠ 0) :
    v₁ ∈ gammaSign (assumeNonzeroAddSign a₁ a₂).1 ∧
    v₂ ∈ gammaSign (assumeNonzeroAddSign a₁ a₂).2 := by
  cases a₁ <;> cases a₂ <;>
    simp [gammaSign, assumeNonzeroAddSign, assumeNonzero] at h₁ h₂ ⊢ <;>
    omega

/-- Backward refinement for addition under zero constraint. -/
def assumeZeroAddSign (a₁ a₂ : Sign) : Sign × Sign :=
  ( match a₂ with
    | .bot => .bot | .zero => assumeZero a₁ | .pos => meetSign a₁ .neg
    | .neg => meetSign a₁ .pos | .nonneg => meetSign a₁ .nonpos
    | .nonpos => meetSign a₁ .nonneg | .top => a₁
  , match a₁ with
    | .bot => .bot | .zero => assumeZero a₂ | .pos => meetSign a₂ .neg
    | .neg => meetSign a₂ .pos | .nonneg => meetSign a₂ .nonpos
    | .nonpos => meetSign a₂ .nonneg | .top => a₂ )

/-- `assumeZeroAddSign` is sound. -/
theorem assumeZeroAddSign_sound
    {a₁ a₂ : Sign}
    {v₁ v₂ : Int}
    (h₁ : v₁ ∈ gammaSign a₁)
    (h₂ : v₂ ∈ gammaSign a₂)
    (hZero : v₁ + v₂ = 0) :
    v₁ ∈ gammaSign (assumeZeroAddSign a₁ a₂).1 ∧
    v₂ ∈ gammaSign (assumeZeroAddSign a₁ a₂).2 := by
  cases a₁ <;> cases a₂ <;>
    simp [gammaSign, assumeZeroAddSign, assumeZero, meetSign,
          signOfFlags, hasNeg, hasZero, hasPos] at h₁ h₂ ⊢ <;>
    omega

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

/-- Gamma-only interface instance for the sign domain. -/
def signGammaDomain :
    AbsInterp.Framework.Domains.GammaDomain Sign Int where
  gamma := gammaSign
  gamma_monotone := gammaSign_monotone_of_leSign
  gamma_top := gammaSign_top
  join_sound := joinSign_sound

end Domains
end AbsInterp
