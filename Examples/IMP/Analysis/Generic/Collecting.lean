import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework
import AbsInterp.Instances.LTS
import Examples.IMP.Analysis.Generic.Soundness

/-!
# Generic IMP unlabeled collecting transfer

Defines a generic unlabeled collecting transfer `transferAnyProgram` for a
fixed IMP program and scalar abstract domain. The transfer over-approximates
every `Step`-firing from any `ActiveIn` source by joining the finitely many
labeled transfer branches that can fire at each program shape.

Together with `soundAny_imp` and the
`{kleeneNat,omegaReachableLTS}_subset_of_isPostFixpoint_imp` corollaries,
this is the IMP adapter into the Session 4 fixpoint bridge (and parallel
to the Session 5 `LTSCollectingAbstraction` path — see the note in
`## Fixpoint bridge for IMP collecting soundness` below for the
packaging trade-off).
-/

namespace Examples.IMP

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Instances.LTS

universe u

variable {A : Type u} [SemilatticeSup A] [OrderTop A] [OrderBot A]
         (d : IMPAnalysisDomain A)

/-- Unlabeled collecting transfer for a fixed IMP program. -/
def transferAnyProgram (d : IMPAnalysisDomain A) :
    Stmt → ConfigSharp A → ConfigSharp A
  | .skip, _ => botConfigSharp
  | .assign x e, κ =>
      transferProgram d (.assign x e) .assign κ
  | .seq s1 s2, κ =>
      joinConfig d.scalarDomain
        (liftSeqConfig s2 (transferAnyProgram d s1 (seqView s2 κ)))
        (joinConfig d.scalarDomain
          (singletonConfig s2 ((seqView s2 κ) .skip))
          (transferAnyProgram d s2 κ))
  | .ite cond s1 s2, κ =>
      joinConfig d.scalarDomain
        (singletonConfig s1 (filterTrueStoreOf d cond (κ (.ite cond s1 s2))))
        (joinConfig d.scalarDomain
          (singletonConfig s2 (filterFalseStoreOf d cond (κ (.ite cond s1 s2))))
          (joinConfig d.scalarDomain
            (transferAnyProgram d s1 κ)
            (transferAnyProgram d s2 κ)))
  | .while cond body, κ =>
      joinConfig d.scalarDomain
        (singletonConfig (.seq body (.while cond body))
          (filterTrueStoreOf d cond (κ (.while cond body))))
        (joinConfig d.scalarDomain
          (singletonConfig .skip (filterFalseStoreOf d cond (κ (.while cond body))))
          (joinConfig d.scalarDomain
            (liftSeqConfig (.while cond body)
              (transferAnyProgram d body (seqView (.while cond body) κ)))
            (singletonConfig (.while cond body)
              ((seqView (.while cond body) κ) .skip))))

/-- Package the unlabeled collecting transfer as a framework one-step transformer. -/
def impCollectingTransfer (d : IMPAnalysisDomain A) (program : Stmt) :
    PostSharp (ConfigSharp A) :=
  transferAnyProgram d program

set_option linter.unusedSectionVars false in
/-- `liftSeqConfig` is monotone in its config argument. -/
theorem liftSeqConfig_mono {s2 : Stmt} {κ₁ κ₂ : ConfigSharp A}
    (h : κ₁ ≤ κ₂) : liftSeqConfig s2 κ₁ ≤ liftSeqConfig s2 κ₂ := by
  intro s x
  cases s with
  | skip => exact le_refl _
  | assign _ _ => exact le_refl _
  | ite _ _ _ => exact le_refl _
  | «while» _ _ => exact le_refl _
  | seq s s2' =>
      by_cases hEq : s2' = s2
      · subst hEq
        simp only [liftSeqConfig, if_true]
        exact h s x
      · simp [liftSeqConfig, hEq]

/--
Coverage lemma: the labeled transfer `transferProgram d program μ κ` is
pointwise `≤` the unlabeled collecting transfer `transferAnyProgram d program κ`.
Proved by structural induction on `program` with case analysis on `μ`.
-/
theorem transferProgram_le_transferAnyProgram :
    ∀ (program : Stmt) (μ : StepLabel) (κ : ConfigSharp A),
      transferProgram d program μ κ ≤ transferAnyProgram d program κ := by
  intro program
  induction program with
  | skip =>
      intro μ κ
      cases μ <;> simp [transferProgram, transferAnyProgram]
  | assign x e =>
      intro μ κ
      cases μ with
      | assign => simp [transferProgram, transferAnyProgram]
      | seqStep _ | seqDone | ifTrue | ifFalse | whileTrue | whileFalse =>
          intro s y
          simp [transferProgram, transferAnyProgram, botConfigSharp, botStoreSharp]
  | seq s1 s2 ih1 ih2 =>
      intro μ κ
      cases μ with
      | assign =>
          intro s y
          simp only [transferProgram]
          have h := ih2 .assign κ s y
          refine le_trans h ?_
          simp only [transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | ifTrue =>
          intro s y
          simp only [transferProgram]
          have h := ih2 .ifTrue κ s y
          refine le_trans h ?_
          simp only [transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | ifFalse =>
          intro s y
          simp only [transferProgram]
          have h := ih2 .ifFalse κ s y
          refine le_trans h ?_
          simp only [transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | whileTrue =>
          intro s y
          simp only [transferProgram]
          have h := ih2 .whileTrue κ s y
          refine le_trans h ?_
          simp only [transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | whileFalse =>
          intro s y
          simp only [transferProgram]
          have h := ih2 .whileFalse κ s y
          refine le_trans h ?_
          simp only [transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | seqDone =>
          -- transferProgram = joinConfig (singletonConfig s2 ((seqView s2 κ) .skip)) (transferProgram d s2 .seqDone κ)
          -- transferAnyProgram = joinConfig (liftSeqConfig s2 (transferAnyProgram d s1 (seqView s2 κ))) (joinConfig (singletonConfig s2 ((seqView s2 κ) .skip)) (transferAnyProgram d s2 κ))
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · -- singletonConfig piece: directly a component of transferAnyProgram
            exact le_sup_of_le_right (le_sup_of_le_left (le_refl _))
          · -- transferProgram d s2 .seqDone κ ≤ transferAnyProgram d s2 κ by IH ≤ the right join
            have h := ih2 .seqDone κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
      | seqStep μ' =>
          -- transferProgram = joinConfig (liftSeqConfig s2 (transferProgram d s1 μ' (seqView s2 κ))) (transferProgram d s2 (.seqStep μ') κ)
          -- transferAnyProgram = joinConfig (liftSeqConfig s2 (transferAnyProgram d s1 (seqView s2 κ))) (...)
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · -- liftSeqConfig monotonicity + IH on s1
            have hs1 := ih1 μ' (seqView s2 κ)
            have hLift := liftSeqConfig_mono (s2 := s2) hs1 s y
            refine le_trans hLift ?_
            exact le_sup_of_le_left (le_refl _)
          · have h := ih2 (.seqStep μ') κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_refl _))
  | ite cond s1 s2 ih1 ih2 =>
      intro μ κ
      cases μ with
      | ifTrue =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ (sup_le ?_ ?_)
          · exact le_sup_of_le_left (le_refl _)
          · have h := ih1 .ifTrue κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .ifTrue κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | ifFalse =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ (sup_le ?_ ?_)
          · exact le_sup_of_le_right (le_sup_of_le_left (le_refl _))
          · have h := ih1 .ifFalse κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .ifFalse κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | assign =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · have h := ih1 .assign κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .assign κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | seqStep μ' =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · have h := ih1 (.seqStep μ') κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 (.seqStep μ') κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | seqDone =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · have h := ih1 .seqDone κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .seqDone κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | whileTrue =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · have h := ih1 .whileTrue κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .whileTrue κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | whileFalse =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine sup_le ?_ ?_
          · have h := ih1 .whileFalse κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
          · have h := ih2 .whileFalse κ s y
            refine le_trans h ?_
            exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
  | «while» cond body ih =>
      intro μ κ
      cases μ with
      | whileTrue =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          exact le_sup_of_le_left (le_refl _)
      | whileFalse =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_left (le_refl _))
      | seqDone =>
          intro s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right (le_refl _)))
      | seqStep μ' =>
          intro s y
          have hBody := ih μ' (seqView (.while cond body) κ)
          have hLift := liftSeqConfig_mono (s2 := .while cond body) hBody s y
          simp only [transferProgram, transferAnyProgram, joinConfig]
          refine le_trans hLift ?_
          exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_left (le_refl _)))
      | assign | ifTrue | ifFalse =>
          intro s y
          simp only [transferProgram, transferAnyProgram, botConfigSharp, botStoreSharp]
          exact bot_le

/--
Monotonicity of `gammaProgram` in the abstract-configuration argument.
-/
theorem gammaProgram_monotone {κ₁ κ₂ : ConfigSharp A} (hLe : κ₁ ≤ κ₂) (program : Stmt) :
    gammaProgram d program κ₁ ⊆ gammaProgram d program κ₂ := by
  rintro c ⟨hActive, hConf⟩
  refine ⟨hActive, ?_⟩
  exact (configConcretizationDomain d.scalarDomain).gamma_monotone hLe hConf

/--
Generic IMP collecting soundness: the unlabeled collecting transfer
`transferAnyProgram` soundly over-approximates `postAny impLTS` w.r.t.
`gammaProgram`.
-/
theorem soundAny_imp (program : Stmt) :
    Sound (postAny impLTS) (gammaProgram d program) (transferAnyProgram d program) := by
  intro κ c' hc'
  rcases (mem_postAny (lts := impLTS) (states := gammaProgram d program κ)
    (s' := c')).1 hc' with ⟨c, hc, μ, htr⟩
  rcases c with ⟨source, σ⟩
  rcases c' with ⟨target, σ'⟩
  rcases hc with ⟨hActive, hStore⟩
  have hLabeled : (target, σ') ∈ gammaProgram d program (transferProgram d program μ κ) :=
    localStepSoundOfActive d hActive hStore htr
  exact gammaProgram_monotone d
    (transferProgram_le_transferAnyProgram d program μ κ) program hLabeled

/-! ## Fixpoint bridge for IMP collecting soundness

`gammaProgram d program` is a `Concretization`, not a `ConcretizationDomain`
(it carries an `ActiveIn` constraint that rules out `gamma_top`). We therefore
package the IMP-side collecting bridge as direct specialisations of the
framework theorems `Iteration.omegaReachable_subset_of_isPostFixpoint` and
`Iteration.kleeneNat_subset_of_isPostFixpoint`, rather than as a strict
`LTSCollectingAbstraction`.
-/

/-- The reach transfer over the generic IMP collecting transfer. -/
def impReachTransfer (d : IMPAnalysisDomain A) (program : Stmt)
    (initAbs : ConfigSharp A) : PostSharp (ConfigSharp A) :=
  fun a => initAbs ⊔ transferAnyProgram d program a

/--
Soundness of the IMP reach transfer with an abstract initial over-approximation.

Whenever a concrete initial set is bounded by `gammaProgram d program initAbs`,
the reach transfer `initAbs ⊔ transferAnyProgram d program ·` is sound w.r.t.
the collecting step `reachF init` on `postAny_collectingStep impLTS`.
-/
theorem sound_impReachTransfer
    (program : Stmt)
    {init : Set Config} {initAbs : ConfigSharp A}
    (hInit : init ⊆ gammaProgram d program initAbs) :
    Sound ((postAny_collectingStep impLTS).reachF init)
      (gammaProgram d program)
      (impReachTransfer d program initAbs) := by
  intro a c hc
  rcases hc with hInitMem | hPostMem
  · -- init contribution
    have hLeft : initAbs ≤ impReachTransfer d program initAbs a := by
      intro s x; exact le_sup_of_le_left (le_refl _)
    exact gammaProgram_monotone d hLeft program (hInit hInitMem)
  · -- postAny contribution
    have hSound : c ∈ gammaProgram d program (transferAnyProgram d program a) :=
      soundAny_imp d program a hPostMem
    have hRight : transferAnyProgram d program a ≤ impReachTransfer d program initAbs a := by
      intro s x; exact le_sup_of_le_right (le_refl _)
    exact gammaProgram_monotone d hRight program hSound

/-- Specialisation of the generic Kleene-iterate bridge to IMP. -/
theorem kleeneNat_subset_of_isPostFixpoint_imp
    (program : Stmt)
    (init : Set Config) (initAbs a : ConfigSharp A)
    (hInit : init ⊆ gammaProgram d program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impReachTransfer d program initAbs) a) :
    ∀ n, (postAny_collectingStep impLTS).kleeneNat init n ⊆ gammaProgram d program a :=
  AbsInterp.Framework.Iteration.kleeneNat_subset_of_isPostFixpoint
    (postAny_collectingStep impLTS) init
    (sound_impReachTransfer d program hInit)
    (fun h => gammaProgram_monotone d h program)
    hFix

/-- Specialisation of the generic ω-reachable bridge to IMP. -/
theorem omegaReachableLTS_subset_of_isPostFixpoint_imp
    (program : Stmt)
    (init : Set Config) (initAbs a : ConfigSharp A)
    (hInit : init ⊆ gammaProgram d program initAbs)
    (hFix : AbsInterp.Framework.Iteration.IsPostFixpoint (· ≤ ·)
      (impReachTransfer d program initAbs) a) :
    omegaReachableLTS impLTS init ⊆ gammaProgram d program a :=
  Set.Subset.trans
    (omegaReachableLTS_subset_omegaReachable impLTS init)
    (AbsInterp.Framework.Iteration.omegaReachable_subset_of_isPostFixpoint
      (postAny_collectingStep impLTS) init
      (sound_impReachTransfer d program hInit)
      (fun h => gammaProgram_monotone d h program)
      hFix)

end Examples.IMP
