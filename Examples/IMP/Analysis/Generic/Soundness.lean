import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework
import AbsInterp.Instances.LTS
import Examples.IMP.Analysis.Generic.Lemmas

namespace Examples.IMP

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Instances.LTS

universe u

variable {A : Type u} [Bot A] [SemilatticeSup A] [OrderTop A] (d : IMPAnalysisDomain A)

/-!
# Generic IMP Soundness Proof

One-step local soundness for the generic IMP transfer, parameterized by
`IMPAnalysisDomain`. This replaces the previously duplicated Sign and
Interval soundness inductions.
-/

theorem localStepSoundOfActive
    {program source : Stmt}
    (hActive : ActiveIn program source) :
    ∀ {κ : ConfigSharp A} {μ : StepLabel} {σ : Store} {target : Stmt} {σ' : Store},
      σ ∈ gammaStoreOf d.scalarDomain.gamma (κ source) →
      Step (source, σ) μ (target, σ') →
      (target, σ') ∈ gammaProgram d program (transferProgram d program μ κ) := by
  induction hActive with
  | skip =>
      intro κ μ σ target σ' hσ hStep
      cases hStep
  | assign =>
      rename_i x e
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | assign =>
          refine ⟨ActiveIn.assignDone, ?_⟩
          have hEval :
              eval σ e ∈ d.scalarDomain.gamma (evalExpr d (κ (.assign x e)) e) :=
            evalExpr_sound d hσ
          have hStore :
              σ.update x (eval σ e) ∈
                gammaStoreOf d.scalarDomain.gamma
                  (updateStoreSharp (κ (.assign x e)) x (evalExpr d (κ (.assign x e)) e)) :=
            mem_gammaStoreOf_updateStoreSharp_of d hσ hEval
          simpa [transferProgram, singletonConfig] using hStore
  | assignDone =>
      rename_i x e
      intro κ μ σ target σ' hσ hStep
      cases hStep
  | seqLeft hInner ih =>
      rename_i s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      cases μ with
      | assign =>
          cases hStep
      | ifTrue =>
          cases hStep
      | ifFalse =>
          cases hStep
      | whileTrue =>
          cases hStep
      | whileFalse =>
          cases hStep
      | seqStep μInner =>
          rcases Step.seqStep_inv hStep with ⟨innerTarget, σInner, hTarget, hStepInner⟩
          have hInnerSound :
              (innerTarget, σInner) ∈
                gammaProgram d s1 (transferProgram d s1 μInner (seqView s2 κ)) :=
            ih (by simpa [seqView] using hσ) hStepInner
          have hLifted :
              (Stmt.seq innerTarget s2, σInner) ∈
                gammaProgram d (.seq s1 s2)
                  (liftSeqConfig s2 (transferProgram d s1 μInner (seqView s2 κ))) :=
            mem_gammaProgram_seqLeft_of d hInnerSound
          cases hTarget
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgram d s1 μInner (seqView s2 κ)))
              (κ₂ := transferProgram d s2 (.seqStep μInner) κ)
              hLifted
      | seqDone =>
          cases hStep
          have hStore : σ ∈ gammaStoreOf d.scalarDomain.gamma ((seqView s2 κ) .skip) := by
            simpa [seqView] using hσ
          have hConf : (s2, σ) ∈ gammaConfigOf d.scalarDomain.gamma (singletonConfig s2 ((seqView s2 κ) .skip)) := by
            simpa [singletonConfig] using hStore
          have hProg :
              (s2, σ) ∈
                gammaProgram d (.seq s1 s2)
                  (singletonConfig s2 ((seqView s2 κ) .skip)) :=
            ⟨ActiveIn.seqRight (ActiveIn.self s2), hConf⟩
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .seq s1 s2)
              (κ₁ := singletonConfig s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgram d s2 .seqDone κ)
              hProg
  | seqRight hInner ih =>
      rename_i s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hRight :
          (target, σ') ∈ gammaProgram d s2 (transferProgram d s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgram d (.seq s1 s2) (transferProgram d s2 μ κ) :=
        mem_gammaProgram_seqRight_of d hRight
      cases μ with
      | assign =>
          simpa [transferProgram] using hWrapped
      | seqStep ν =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgram d s1 ν (seqView s2 κ)))
              (κ₂ := transferProgram d s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .seq s1 s2)
              (κ₁ := singletonConfig s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgram d s2 .seqDone κ)
              hWrapped
      | ifTrue =>
          simpa [transferProgram] using hWrapped
      | ifFalse =>
          simpa [transferProgram] using hWrapped
      | whileTrue =>
          simpa [transferProgram] using hWrapped
      | whileFalse =>
          simpa [transferProgram] using hWrapped
  | iteRoot =>
      rename_i cond s1 s2
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | if_true hCond =>
          have hStore :
              σ ∈ gammaStoreOf d.scalarDomain.gamma (filterTrueStoreOf d cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_filterTrueStoreOf d hσ hCond
          have hRoot :
              (s1, σ) ∈
                gammaProgram d (.ite cond s1 s2)
                  (singletonConfig s1 (filterTrueStoreOf d cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteThen (ActiveIn.self s1), ?_⟩
            simpa [singletonConfig] using hStore
          have hJoin :
              (s1, σ) ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (singletonConfig s1 (filterTrueStoreOf d cond (κ (.ite cond s1 s2))))
                    (joinConfig d.scalarDomain
                      (transferProgram d s1 .ifTrue κ)
                      (transferProgram d s2 .ifTrue κ))) :=
            mem_gammaProgram_join_left_of d hRoot
          simpa [transferProgram] using hJoin
      | if_false hCond =>
          have hStore :
              σ ∈ gammaStoreOf d.scalarDomain.gamma (filterFalseStoreOf d cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_filterFalseStoreOf d hσ hCond
          have hRoot :
              (s2, σ) ∈
                gammaProgram d (.ite cond s1 s2)
                  (singletonConfig s2 (filterFalseStoreOf d cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteElse (ActiveIn.self s2), ?_⟩
            simpa [singletonConfig] using hStore
          have hJoin :
              (s2, σ) ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (singletonConfig s2 (filterFalseStoreOf d cond (κ (.ite cond s1 s2))))
                    (joinConfig d.scalarDomain
                      (transferProgram d s1 .ifFalse κ)
                      (transferProgram d s2 .ifFalse κ))) :=
            mem_gammaProgram_join_left_of d hRoot
          simpa [transferProgram] using hJoin
  | iteThen hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hThen :
          (target, σ') ∈ gammaProgram d s1 (transferProgram d s1 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgram d (.ite cond s1 s2) (transferProgram d s1 μ κ) :=
        mem_gammaProgram_iteThen_of d hThen
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (transferProgram d s1 .ifTrue κ)
                    (transferProgram d s2 .ifTrue κ)) :=
            mem_gammaProgram_join_left_of d hWrapped
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfig s1 (filterTrueStoreOf d cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfig d.scalarDomain
                (transferProgram d s1 .ifTrue κ)
                (transferProgram d s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (transferProgram d s1 .ifFalse κ)
                    (transferProgram d s2 .ifFalse κ)) :=
            mem_gammaProgram_join_left_of d hWrapped
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfig s2 (filterFalseStoreOf d cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfig d.scalarDomain
                (transferProgram d s1 .ifFalse κ)
                (transferProgram d s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .assign κ)
              (κ₂ := transferProgram d s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 (.seqStep ν) κ)
              (κ₂ := transferProgram d s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .seqDone κ)
              (κ₂ := transferProgram d s2 .seqDone κ)
              hWrapped
      | whileTrue =>
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .whileTrue κ)
              (κ₂ := transferProgram d s2 .whileTrue κ)
              hWrapped
      | whileFalse =>
          simpa [transferProgram] using
            mem_gammaProgram_join_left_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .whileFalse κ)
              (κ₂ := transferProgram d s2 .whileFalse κ)
              hWrapped
  | iteElse hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hElse :
          (target, σ') ∈ gammaProgram d s2 (transferProgram d s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgram d (.ite cond s1 s2) (transferProgram d s2 μ κ) :=
        mem_gammaProgram_iteElse_of d hElse
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (transferProgram d s1 .ifTrue κ)
                    (transferProgram d s2 .ifTrue κ)) :=
            mem_gammaProgram_join_right_of d hWrapped
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfig s1 (filterTrueStoreOf d cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfig d.scalarDomain
                (transferProgram d s1 .ifTrue κ)
                (transferProgram d s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgram d (.ite cond s1 s2)
                  (joinConfig d.scalarDomain
                    (transferProgram d s1 .ifFalse κ)
                    (transferProgram d s2 .ifFalse κ)) :=
            mem_gammaProgram_join_right_of d hWrapped
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfig s2 (filterFalseStoreOf d cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfig d.scalarDomain
                (transferProgram d s1 .ifFalse κ)
                (transferProgram d s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .assign κ)
              (κ₂ := transferProgram d s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 (.seqStep ν) κ)
              (κ₂ := transferProgram d s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .seqDone κ)
              (κ₂ := transferProgram d s2 .seqDone κ)
              hWrapped
      | whileTrue =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .whileTrue κ)
              (κ₂ := transferProgram d s2 .whileTrue κ)
              hWrapped
      | whileFalse =>
          simpa [transferProgram] using
            mem_gammaProgram_join_right_of d
              (program := .ite cond s1 s2)
              (κ₁ := transferProgram d s1 .whileFalse κ)
              (κ₂ := transferProgram d s2 .whileFalse κ)
              hWrapped
  | whileRoot =>
      rename_i cond body
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | while_true hCond =>
          have hStore :
              σ ∈ gammaStoreOf d.scalarDomain.gamma (filterTrueStoreOf d cond (κ (.while cond body))) :=
            mem_gammaStoreOf_filterTrueStoreOf d hσ hCond
          have hRoot :
              (.seq body (.while cond body), σ) ∈
                gammaProgram d (.while cond body)
                  (singletonConfig (.seq body (.while cond body))
                    (filterTrueStoreOf d cond (κ (.while cond body)))) := by
            refine ⟨ActiveIn.whileBody (ActiveIn.self body), ?_⟩
            simpa [singletonConfig] using hStore
          simpa [transferProgram] using hRoot
      | while_false hCond =>
          have hStore :
              σ ∈ gammaStoreOf d.scalarDomain.gamma (filterFalseStoreOf d cond (κ (.while cond body))) :=
            mem_gammaStoreOf_filterFalseStoreOf d hσ hCond
          have hRoot :
              (.skip, σ) ∈
                gammaProgram d (.while cond body)
                  (singletonConfig .skip
                    (filterFalseStoreOf d cond (κ (.while cond body)))) := by
            refine ⟨ActiveIn.whileDone, ?_⟩
            simpa [singletonConfig] using hStore
          simpa [transferProgram] using hRoot
  | whileDone =>
      rename_i cond body
      intro κ μ σ target σ' hσ hStep
      cases hStep
  | whileBody hInner ih =>
      rename_i cond body inner
      intro κ μ σ target σ' hσ hStep
      cases μ with
      | assign =>
          cases hStep
      | ifTrue =>
          cases hStep
      | ifFalse =>
          cases hStep
      | whileTrue =>
          cases hStep
      | whileFalse =>
          cases hStep
      | seqStep μInner =>
          rcases Step.seqStep_inv hStep with ⟨innerTarget, σInner, hTarget, hStepInner⟩
          have hInnerSound :
              (innerTarget, σInner) ∈
                gammaProgram d body (transferProgram d body μInner (seqView (.while cond body) κ)) :=
            ih (by simpa [seqView] using hσ) hStepInner
          have hLifted :
              (Stmt.seq innerTarget (.while cond body), σInner) ∈
                gammaProgram d (.while cond body)
                  (liftSeqConfig (.while cond body) (transferProgram d body μInner (seqView (.while cond body) κ))) := by
            rcases hInnerSound with ⟨hActiveInner, hConfInner⟩
            exact ⟨ActiveIn.whileBody hActiveInner, mem_gammaConfigOf_liftSeqConfig_of d hConfInner⟩
          cases hTarget
          simpa [transferProgram] using hLifted
      | seqDone =>
          cases hStep
          have hStore : σ ∈ gammaStoreOf d.scalarDomain.gamma ((seqView (.while cond body) κ) .skip) := by
            simpa [seqView] using hσ
          have hProg :
              (.while cond body, σ) ∈
                gammaProgram d (.while cond body)
                  (singletonConfig (.while cond body) ((seqView (.while cond body) κ) .skip)) := by
            refine ⟨ActiveIn.whileRoot, ?_⟩
            simpa [singletonConfig] using hStore
          simpa [transferProgram] using hProg

/-- One-step soundness of the generic transfer over the canonical labeled IMP LTS. -/
theorem soundStep_imp
    (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgram d program) (impTransfer d program) := by
  intro μ κ c' hc'
  rcases (Cslib.LTS.mem_setImage
    (lts := impLTS)
    (S := gammaProgram d program κ)
    (μ := μ)
    (s' := c')).1 (by simpa [postStep] using hc') with
      ⟨c, hc, hStep⟩
  rcases c with ⟨source, σ⟩
  rcases c' with ⟨target, σ'⟩
  rcases hc with ⟨hActive, hStore⟩
  simpa [impTransfer] using
    (localStepSoundOfActive d hActive hStore hStep)

/-- LTS abstraction packaging the generic IMP analysis for a fixed program and domain. -/
def impAbstraction
    (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp A) :=
  LTSAbstraction.ofExplicit
    impLTS
    (gammaProgram d program)
    (impTransfer d program)
    (soundStep_imp d program)

end Examples.IMP
