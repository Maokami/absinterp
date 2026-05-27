import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp

namespace Tests
namespace InstancesLTSCollectingHook

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Framework.Iteration
open AbsInterp.Instances.LTS
open AbsInterp.Instances.LTS.Analyses

/-!
# CollectingHook smoke test

Exercises the Session 5 LTS collecting/fixpoint bridge on a toy looping
LTS with a constant-top abstract domain. Proves that every ω-reachable
state of the LTS is concretized by the abstract post-fixpoint,
using:

- `LTSCollectingAbstraction` (new collecting interface)
- `CollectingSoundOfRead` + `collectingAbstractionOfCollectingSound`
  (new readout helper)
- `LTSCollectingAbstraction.omegaReachableLTS_subset_of_isPostFixpoint`
  (new LTS omega bridge)
-/

/-- Toy LTS: `0 →()→ 1`, `1 →()→ 0`. -/
def loopLTS : Cslib.LTS Nat Unit where
  Tr s _ s' := (s = 0 ∧ s' = 1) ∨ (s = 1 ∧ s' = 0)

/-- Minimal two-element abstract domain: `bot ≤ top`. -/
inductive Top2 where
  | bot
  | top
  deriving DecidableEq, Repr

namespace Top2

def le : Top2 -> Top2 -> Prop
  | .bot, _ => True
  | .top, .top => True
  | .top, .bot => False

theorem le_refl : ∀ a : Top2, le a a := by
  intro a; cases a <;> simp [le]

theorem le_trans : ∀ {a b c : Top2}, le a b -> le b c -> le a c := by
  intro a b c hab hbc; cases a <;> cases b <;> cases c <;> simp_all [le]

theorem le_antisymm : ∀ {a b : Top2}, le a b -> le b a -> a = b := by
  intro a b hab hba; cases a <;> cases b <;> simp_all [le]

instance : PartialOrder Top2 where
  le := le
  le_refl := le_refl
  le_trans := @le_trans
  le_antisymm _ _ := le_antisymm

instance : OrderTop Top2 where
  top := .top
  le_top a := by cases a <;> simp [LE.le, le]

/-- Join: `bot ⊔ a = a`, otherwise `top`. -/
def sup : Top2 -> Top2 -> Top2
  | .bot, a => a
  | a, .bot => a
  | _, _ => .top

theorem le_sup_left : ∀ a b : Top2, a ≤ sup a b := by
  intro a b; cases a <;> cases b <;> simp [LE.le, le, sup]

theorem le_sup_right : ∀ a b : Top2, b ≤ sup a b := by
  intro a b; cases a <;> cases b <;> simp [LE.le, le, sup]

theorem sup_le : ∀ {a b c : Top2}, a ≤ c -> b ≤ c -> sup a b ≤ c := by
  intro a b c hac hbc; cases a <;> cases b <;> cases c <;> simp_all [LE.le, le, sup]

instance : SemilatticeSup Top2 where
  sup := sup
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le _ _ _ ha hb := sup_le ha hb

/-- Constant-top concretization over any observation type. -/
def gamma {Observation : Type} : Top2 -> Set Observation
  | .bot => ∅
  | .top => Set.univ

theorem gamma_monotone {Observation : Type} :
    ∀ ⦃a b : Top2⦄, a ≤ b -> (gamma a : Set Observation) ⊆ gamma b := by
  intro a b hab; cases a <;> cases b <;> simp_all [LE.le, le, gamma]

def concretization (Observation : Type) :
    ConcretizationDomain Top2 Observation where
  gamma := gamma
  gamma_monotone := gamma_monotone
  gamma_top _ := Set.mem_univ _

end Top2

/-! ## Building the collecting abstraction via the readout helper -/

/-- Read states as themselves (into Nat as the observation). -/
def readId : Nat -> Nat := fun s => s

/-- Transfer: always jump to `.top`. -/
def transferAnyToy : PostSharp Top2 := fun _ => .top

/-- `transferAnyToy` is collecting-sound via readout. -/
theorem collectingSoundToy :
    CollectingSoundOfRead (Top2.gamma (Observation := Nat)) loopLTS readId transferAnyToy := by
  intro a s s' _ _
  simp [transferAnyToy, gammaStateOfRead, Top2.gamma]

/-- Build the collecting abstraction via the readout helper. -/
def toyCollecting : LTSCollectingAbstraction Nat Unit Top2 :=
  collectingAbstractionOfCollectingSound
    (Top2.concretization Nat) loopLTS readId transferAnyToy collectingSoundToy

/-! ## Using the bridge to conclude omega-reachability safety -/

/-- `.top` is a post-fixpoint of the reachability transfer. -/
theorem toy_isPostFixpoint :
    IsPostFixpoint (· ≤ ·) (toyCollecting.reachTransfer .top) .top := by
  simp [IsPostFixpoint, LTSCollectingAbstraction.reachTransfer, reachTransferAny,
        transferAnyToy, toyCollecting, collectingAbstractionOfCollectingSound]

/-- Any initial concrete set is bounded by `.top`. -/
theorem init_subset_gammaTop (init : Set Nat) :
    init ⊆ (toyCollecting.domain.gamma .top : Set Nat) := by
  intro s _; exact Set.mem_univ _

/-- Headline: every ω-reachable state is concretized by the post-fixpoint. -/
example :
    omegaReachableLTS loopLTS {0} ⊆ toyCollecting.domain.gamma .top :=
  LTSCollectingAbstraction.omegaReachableLTS_subset_of_isPostFixpoint
    toyCollecting {0} .top .top
    (init_subset_gammaTop {0}) toy_isPostFixpoint

/-- Corollary: every finite Kleene iterate is concretized by the post-fixpoint. -/
example :
    ∀ n, (postAny_collectingStep loopLTS).kleeneNat {0} n ⊆
      toyCollecting.domain.gamma .top :=
  LTSCollectingAbstraction.kleeneNat_subset_of_isPostFixpoint
    toyCollecting {0} .top .top
    (init_subset_gammaTop {0}) toy_isPostFixpoint

end InstancesLTSCollectingHook
end Tests
