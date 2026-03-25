import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Domains
import AbsInterpLTS.Framework
import AbsInterpLTS.Instances.LTS
import Examples.IMP.Analysis.Interval.Lemmas

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

theorem localStepSoundIntervalOfActive
    {program source : Stmt}
    (hActive : ActiveIn program source) :
    ∀ {κ : ConfigSharp Interval} {μ : StepLabel} {σ : Store} {target : Stmt} {σ' : Store},
      σ ∈ gammaStoreOf gammaInterval (κ source) →
      Step (source, σ) μ (target, σ') →
      (target, σ') ∈ gammaProgramInterval program (transferProgramInterval program μ κ) := by
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
              eval σ e ∈ gammaInterval (evalIntervalExpr (κ (.assign x e)) e) :=
            evalIntervalExpr_sound hσ
          have hStore :
              σ.update x (eval σ e) ∈
                gammaStoreOf gammaInterval
                  (updateStoreSharp (κ (.assign x e)) x (evalIntervalExpr (κ (.assign x e)) e)) :=
            mem_gammaStoreOf_updateStoreSharp_interval hσ hEval
          simpa [transferProgramInterval, singletonConfigInterval, singletonConfig] using hStore
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
      | seqStep μInner =>
          rcases Step.seqStep_inv hStep with ⟨innerTarget, σInner, hTarget, hStepInner⟩
          have hInnerSound :
              (innerTarget, σInner) ∈
                gammaProgramInterval s1 (transferProgramInterval s1 μInner (seqView s2 κ)) :=
            ih (by simpa [seqView] using hσ) hStepInner
          have hLifted :
              (Stmt.seq innerTarget s2, σInner) ∈
                gammaProgramInterval (.seq s1 s2)
                  (liftSeqConfig s2 (transferProgramInterval s1 μInner (seqView s2 κ))) :=
            mem_gammaProgram_seqLeft_interval hInnerSound
          cases hTarget
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_left_interval
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgramInterval s1 μInner (seqView s2 κ)))
              (κ₂ := transferProgramInterval s2 (.seqStep μInner) κ)
              hLifted
      | seqDone =>
          cases hStep
          have hStore : σ ∈ gammaStoreOf gammaInterval ((seqView s2 κ) .skip) := by
            simpa [seqView] using hσ
          have hConf : (s2, σ) ∈ gammaConfigOf gammaInterval (singletonConfigInterval s2 ((seqView s2 κ) .skip)) := by
            simpa [singletonConfigInterval, singletonConfig] using hStore
          have hProg :
              (s2, σ) ∈
                gammaProgramInterval (.seq s1 s2)
                  (singletonConfigInterval s2 ((seqView s2 κ) .skip)) :=
            ⟨ActiveIn.seqRight (ActiveIn.self s2), hConf⟩
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_left_interval
              (program := .seq s1 s2)
              (κ₁ := singletonConfigInterval s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgramInterval s2 .seqDone κ)
              hProg
  | seqRight hInner ih =>
      rename_i s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hRight :
          (target, σ') ∈ gammaProgramInterval s2 (transferProgramInterval s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramInterval (.seq s1 s2) (transferProgramInterval s2 μ κ) :=
        mem_gammaProgram_seqRight_interval hRight
      cases μ with
      | assign =>
          simpa [transferProgramInterval] using hWrapped
      | seqStep ν =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgramInterval s1 ν (seqView s2 κ)))
              (κ₂ := transferProgramInterval s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .seq s1 s2)
              (κ₁ := singletonConfigInterval s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgramInterval s2 .seqDone κ)
              hWrapped
      | ifTrue =>
          simpa [transferProgramInterval] using hWrapped
      | ifFalse =>
          simpa [transferProgramInterval] using hWrapped
  | iteRoot =>
      rename_i cond s1 s2
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | if_true hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaInterval (assumeTrueStoreInterval cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_assumeTrueStoreInterval hσ hCond
          have hRoot :
              (s1, σ) ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (singletonConfigInterval s1 (assumeTrueStoreInterval cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteThen (ActiveIn.self s1), ?_⟩
            simpa [singletonConfigInterval, singletonConfig] using hStore
          have hJoin :
              (s1, σ) ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (singletonConfigInterval s1 (assumeTrueStoreInterval cond (κ (.ite cond s1 s2))))
                    (joinConfigInterval
                      (transferProgramInterval s1 .ifTrue κ)
                      (transferProgramInterval s2 .ifTrue κ))) :=
            mem_gammaProgram_join_left_interval hRoot
          simpa [transferProgramInterval] using hJoin
      | if_false hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaInterval (assumeFalseStoreInterval cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_assumeFalseStoreInterval hσ hCond
          have hRoot :
              (s2, σ) ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (singletonConfigInterval s2 (assumeFalseStoreInterval cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteElse (ActiveIn.self s2), ?_⟩
            simpa [singletonConfigInterval, singletonConfig] using hStore
          have hJoin :
              (s2, σ) ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (singletonConfigInterval s2 (assumeFalseStoreInterval cond (κ (.ite cond s1 s2))))
                    (joinConfigInterval
                      (transferProgramInterval s1 .ifFalse κ)
                      (transferProgramInterval s2 .ifFalse κ))) :=
            mem_gammaProgram_join_left_interval hRoot
          simpa [transferProgramInterval] using hJoin
  | iteThen hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hThen :
          (target, σ') ∈ gammaProgramInterval s1 (transferProgramInterval s1 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramInterval (.ite cond s1 s2) (transferProgramInterval s1 μ κ) :=
        mem_gammaProgram_iteThen_interval hThen
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (transferProgramInterval s1 .ifTrue κ)
                    (transferProgramInterval s2 .ifTrue κ)) :=
            mem_gammaProgram_join_left_interval hWrapped
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigInterval s1 (assumeTrueStoreInterval cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigInterval
                (transferProgramInterval s1 .ifTrue κ)
                (transferProgramInterval s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (transferProgramInterval s1 .ifFalse κ)
                    (transferProgramInterval s2 .ifFalse κ)) :=
            mem_gammaProgram_join_left_interval hWrapped
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigInterval s2 (assumeFalseStoreInterval cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigInterval
                (transferProgramInterval s1 .ifFalse κ)
                (transferProgramInterval s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_left_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 .assign κ)
              (κ₂ := transferProgramInterval s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_left_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 (.seqStep ν) κ)
              (κ₂ := transferProgramInterval s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_left_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 .seqDone κ)
              (κ₂ := transferProgramInterval s2 .seqDone κ)
              hWrapped
  | iteElse hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hElse :
          (target, σ') ∈ gammaProgramInterval s2 (transferProgramInterval s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramInterval (.ite cond s1 s2) (transferProgramInterval s2 μ κ) :=
        mem_gammaProgram_iteElse_interval hElse
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (transferProgramInterval s1 .ifTrue κ)
                    (transferProgramInterval s2 .ifTrue κ)) :=
            mem_gammaProgram_join_right_interval hWrapped
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigInterval s1 (assumeTrueStoreInterval cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigInterval
                (transferProgramInterval s1 .ifTrue κ)
                (transferProgramInterval s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramInterval (.ite cond s1 s2)
                  (joinConfigInterval
                    (transferProgramInterval s1 .ifFalse κ)
                    (transferProgramInterval s2 .ifFalse κ)) :=
            mem_gammaProgram_join_right_interval hWrapped
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigInterval s2 (assumeFalseStoreInterval cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigInterval
                (transferProgramInterval s1 .ifFalse κ)
                (transferProgramInterval s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 .assign κ)
              (κ₂ := transferProgramInterval s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 (.seqStep ν) κ)
              (κ₂ := transferProgramInterval s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramInterval] using
            mem_gammaProgram_join_right_interval
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramInterval s1 .seqDone κ)
              (κ₂ := transferProgramInterval s2 .seqDone κ)
              hWrapped

/-- One-step soundness of the generic Interval transfer over the canonical labeled IMP LTS. -/
theorem soundStep_impInterval
    (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgramInterval program) (impIntervalTransfer program) := by
  intro μ κ c' hc'
  rcases (Cslib.LTS.mem_setImage
    (lts := impLTS)
    (S := gammaProgramInterval program κ)
    (μ := μ)
    (s' := c')).1 (by simpa [postStep] using hc') with
      ⟨c, hc, hStep⟩
  rcases c with ⟨source, σ⟩
  rcases c' with ⟨target, σ'⟩
  rcases hc with ⟨hActive, hStore⟩
  simpa [impIntervalTransfer] using
    (localStepSoundIntervalOfActive hActive hStore hStep)

/-- LTS abstraction packaging the generic Interval IMP analysis for a fixed program. -/
def impIntervalAbstraction
    (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp Interval) :=
  LTSAbstraction.ofExplicit
    impLTS
    (gammaProgramInterval program)
    (impIntervalTransfer program)
    (soundStep_impInterval program)

end Examples.IMP
