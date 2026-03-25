import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Domains
import AbsInterpLTS.Framework
import AbsInterpLTS.Instances.LTS
import Examples.IMP.Analysis.Sign.Lemmas

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

theorem localStepSoundSignOfActive
    {program source : Stmt}
    (hActive : ActiveIn program source) :
    ∀ {κ : ConfigSharp Sign} {μ : StepLabel} {σ : Store} {target : Stmt} {σ' : Store},
      σ ∈ gammaStoreOf gammaSign (κ source) →
      Step (source, σ) μ (target, σ') →
      (target, σ') ∈ gammaProgramSign program (transferProgramSign program μ κ) := by
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
              eval σ e ∈ gammaSign (evalSignExpr (κ (.assign x e)) e) :=
            evalSignExpr_sound hσ
          have hStore :
              σ.update x (eval σ e) ∈
                gammaStoreOf gammaSign
                  (updateStoreSharp (κ (.assign x e)) x (evalSignExpr (κ (.assign x e)) e)) :=
            mem_gammaStoreOf_updateStoreSharp hσ hEval
          simpa [transferProgramSign, singletonConfigSign] using hStore
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
                gammaProgramSign s1 (transferProgramSign s1 μInner (seqView s2 κ)) :=
            ih (by simpa [seqView] using hσ) hStepInner
          have hLifted :
              (Stmt.seq innerTarget s2, σInner) ∈
                gammaProgramSign (.seq s1 s2)
                  (liftSeqConfig s2 (transferProgramSign s1 μInner (seqView s2 κ))) :=
            mem_gammaProgram_seqLeft hInnerSound
          cases hTarget
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgramSign s1 μInner (seqView s2 κ)))
              (κ₂ := transferProgramSign s2 (.seqStep μInner) κ)
              hLifted
      | seqDone =>
          cases hStep
          have hStore : σ ∈ gammaStoreOf gammaSign ((seqView s2 κ) .skip) := by
            simpa [seqView] using hσ
          have hConf : (s2, σ) ∈ gammaConfigOf gammaSign (singletonConfigSign s2 ((seqView s2 κ) .skip)) := by
            simpa [singletonConfigSign] using hStore
          have hProg :
              (s2, σ) ∈
                gammaProgramSign (.seq s1 s2)
                  (singletonConfigSign s2 ((seqView s2 κ) .skip)) :=
            ⟨ActiveIn.seqRight (ActiveIn.self s2), hConf⟩
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .seq s1 s2)
              (κ₁ := singletonConfigSign s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgramSign s2 .seqDone κ)
              hProg
  | seqRight hInner ih =>
      rename_i s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hRight :
          (target, σ') ∈ gammaProgramSign s2 (transferProgramSign s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramSign (.seq s1 s2) (transferProgramSign s2 μ κ) :=
        mem_gammaProgram_seqRight hRight
      cases μ with
      | assign =>
          simpa [transferProgramSign] using hWrapped
      | seqStep ν =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .seq s1 s2)
              (κ₁ := liftSeqConfig s2 (transferProgramSign s1 ν (seqView s2 κ)))
              (κ₂ := transferProgramSign s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .seq s1 s2)
              (κ₁ := singletonConfigSign s2 ((seqView s2 κ) .skip))
              (κ₂ := transferProgramSign s2 .seqDone κ)
              hWrapped
      | ifTrue =>
          simpa [transferProgramSign] using hWrapped
      | ifFalse =>
          simpa [transferProgramSign] using hWrapped
      | whileTrue =>
          simpa [transferProgramSign] using hWrapped
      | whileFalse =>
          simpa [transferProgramSign] using hWrapped
  | iteRoot =>
      rename_i cond s1 s2
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | if_true hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaSign (assumeTrueStore cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_assumeTrueStore hσ hCond
          have hRoot :
              (s1, σ) ∈
                gammaProgramSign (.ite cond s1 s2)
                  (singletonConfigSign s1 (assumeTrueStore cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteThen (ActiveIn.self s1), ?_⟩
            simpa [singletonConfigSign] using hStore
          have hJoin :
              (s1, σ) ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (singletonConfigSign s1 (assumeTrueStore cond (κ (.ite cond s1 s2))))
                    (joinConfigSign
                      (transferProgramSign s1 .ifTrue κ)
                      (transferProgramSign s2 .ifTrue κ))) :=
            mem_gammaProgram_join_left hRoot
          simpa [transferProgramSign] using hJoin
      | if_false hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaSign (assumeFalseStore cond (κ (.ite cond s1 s2))) :=
            mem_gammaStoreOf_assumeFalseStore hσ hCond
          have hRoot :
              (s2, σ) ∈
                gammaProgramSign (.ite cond s1 s2)
                  (singletonConfigSign s2 (assumeFalseStore cond (κ (.ite cond s1 s2)))) := by
            refine ⟨ActiveIn.iteElse (ActiveIn.self s2), ?_⟩
            simpa [singletonConfigSign] using hStore
          have hJoin :
              (s2, σ) ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (singletonConfigSign s2 (assumeFalseStore cond (κ (.ite cond s1 s2))))
                    (joinConfigSign
                      (transferProgramSign s1 .ifFalse κ)
                      (transferProgramSign s2 .ifFalse κ))) :=
            mem_gammaProgram_join_left hRoot
          simpa [transferProgramSign] using hJoin
  | iteThen hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hThen :
          (target, σ') ∈ gammaProgramSign s1 (transferProgramSign s1 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramSign (.ite cond s1 s2) (transferProgramSign s1 μ κ) :=
        mem_gammaProgram_iteThen hThen
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (transferProgramSign s1 .ifTrue κ)
                    (transferProgramSign s2 .ifTrue κ)) :=
            mem_gammaProgram_join_left hWrapped
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigSign s1 (assumeTrueStore cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigSign
                (transferProgramSign s1 .ifTrue κ)
                (transferProgramSign s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (transferProgramSign s1 .ifFalse κ)
                    (transferProgramSign s2 .ifFalse κ)) :=
            mem_gammaProgram_join_left hWrapped
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigSign s2 (assumeFalseStore cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigSign
                (transferProgramSign s1 .ifFalse κ)
                (transferProgramSign s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .assign κ)
              (κ₂ := transferProgramSign s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 (.seqStep ν) κ)
              (κ₂ := transferProgramSign s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .seqDone κ)
              (κ₂ := transferProgramSign s2 .seqDone κ)
              hWrapped
      | whileTrue =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .whileTrue κ)
              (κ₂ := transferProgramSign s2 .whileTrue κ)
              hWrapped
      | whileFalse =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_left
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .whileFalse κ)
              (κ₂ := transferProgramSign s2 .whileFalse κ)
              hWrapped
  | iteElse hInner ih =>
      rename_i cond s1 s2 inner
      intro κ μ σ target σ' hσ hStep
      have hElse :
          (target, σ') ∈ gammaProgramSign s2 (transferProgramSign s2 μ κ) :=
        ih hσ hStep
      have hWrapped : (target, σ') ∈ gammaProgramSign (.ite cond s1 s2) (transferProgramSign s2 μ κ) :=
        mem_gammaProgram_iteElse hElse
      cases μ with
      | ifTrue =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (transferProgramSign s1 .ifTrue κ)
                    (transferProgramSign s2 .ifTrue κ)) :=
            mem_gammaProgram_join_right hWrapped
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigSign s1 (assumeTrueStore cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigSign
                (transferProgramSign s1 .ifTrue κ)
                (transferProgramSign s2 .ifTrue κ))
              hInnerJoin
      | ifFalse =>
          have hInnerJoin :
              (target, σ') ∈
                gammaProgramSign (.ite cond s1 s2)
                  (joinConfigSign
                    (transferProgramSign s1 .ifFalse κ)
                    (transferProgramSign s2 .ifFalse κ)) :=
            mem_gammaProgram_join_right hWrapped
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := singletonConfigSign s2 (assumeFalseStore cond (κ (.ite cond s1 s2))))
              (κ₂ := joinConfigSign
                (transferProgramSign s1 .ifFalse κ)
                (transferProgramSign s2 .ifFalse κ))
              hInnerJoin
      | assign =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .assign κ)
              (κ₂ := transferProgramSign s2 .assign κ)
              hWrapped
      | seqStep ν =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 (.seqStep ν) κ)
              (κ₂ := transferProgramSign s2 (.seqStep ν) κ)
              hWrapped
      | seqDone =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .seqDone κ)
              (κ₂ := transferProgramSign s2 .seqDone κ)
              hWrapped
      | whileTrue =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .whileTrue κ)
              (κ₂ := transferProgramSign s2 .whileTrue κ)
              hWrapped
      | whileFalse =>
          simpa [transferProgramSign] using
            mem_gammaProgram_join_right
              (program := .ite cond s1 s2)
              (κ₁ := transferProgramSign s1 .whileFalse κ)
              (κ₂ := transferProgramSign s2 .whileFalse κ)
              hWrapped
  | whileRoot =>
      rename_i cond body
      intro κ μ σ target σ' hσ hStep
      cases hStep with
      | while_true hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaSign (assumeTrueStore cond (κ (.while cond body))) :=
            mem_gammaStoreOf_assumeTrueStore hσ hCond
          have hRoot :
              (.seq body (.while cond body), σ) ∈
                gammaProgramSign (.while cond body)
                  (singletonConfigSign (.seq body (.while cond body))
                    (assumeTrueStore cond (κ (.while cond body)))) := by
            refine ⟨ActiveIn.whileBody (ActiveIn.self body), ?_⟩
            simpa [singletonConfigSign] using hStore
          simpa [transferProgramSign] using hRoot
      | while_false hCond =>
          have hStore :
              σ ∈ gammaStoreOf gammaSign (assumeFalseStore cond (κ (.while cond body))) :=
            mem_gammaStoreOf_assumeFalseStore hσ hCond
          have hRoot :
              (.skip, σ) ∈
                gammaProgramSign (.while cond body)
                  (singletonConfigSign .skip
                    (assumeFalseStore cond (κ (.while cond body)))) := by
            refine ⟨ActiveIn.whileDone, ?_⟩
            simpa [singletonConfigSign] using hStore
          simpa [transferProgramSign] using hRoot
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
                gammaProgramSign body (transferProgramSign body μInner (seqView (.while cond body) κ)) :=
            ih (by simpa [seqView] using hσ) hStepInner
          have hLifted :
              (Stmt.seq innerTarget (.while cond body), σInner) ∈
                gammaProgramSign (.while cond body)
                  (liftSeqConfig (.while cond body) (transferProgramSign body μInner (seqView (.while cond body) κ))) := by
            rcases hInnerSound with ⟨hActiveInner, hConfInner⟩
            exact ⟨ActiveIn.whileBody hActiveInner, mem_gammaConfigOf_liftSeqConfig hConfInner⟩
          cases hTarget
          simpa [transferProgramSign] using hLifted
      | seqDone =>
          cases hStep
          have hStore : σ ∈ gammaStoreOf gammaSign ((seqView (.while cond body) κ) .skip) := by
            simpa [seqView] using hσ
          have hProg :
              (.while cond body, σ) ∈
                gammaProgramSign (.while cond body)
                  (singletonConfigSign (.while cond body) ((seqView (.while cond body) κ) .skip)) := by
            refine ⟨ActiveIn.whileRoot, ?_⟩
            simpa [singletonConfigSign] using hStore
          simpa [transferProgramSign] using hProg

/-- One-step soundness of the generic Sign transfer over the canonical labeled IMP LTS. -/
theorem soundStep_impSign
    (program : Stmt) :
    SoundStep (postStep impLTS) (gammaProgramSign program) (impSignTransfer program) := by
  intro μ κ c' hc'
  rcases (Cslib.LTS.mem_setImage
    (lts := impLTS)
    (S := gammaProgramSign program κ)
    (μ := μ)
    (s' := c')).1 (by simpa [postStep] using hc') with
      ⟨c, hc, hStep⟩
  rcases c with ⟨source, σ⟩
  rcases c' with ⟨target, σ'⟩
  rcases hc with ⟨hActive, hStore⟩
  simpa [impSignTransfer] using
    (localStepSoundSignOfActive hActive hStore hStep)

/-- LTS abstraction packaging the generic Sign IMP analysis for a fixed program. -/
def impSignAbstraction
    (program : Stmt) :
    LTSAbstraction Config StepLabel (ConfigSharp Sign) :=
  LTSAbstraction.ofExplicit
    impLTS
    (gammaProgramSign program)
    (impSignTransfer program)
    (soundStep_impSign program)

end Examples.IMP
