import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS
import Examples.IMP.Analysis.Sign.Defs

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

@[simp] theorem mem_gammaStoreOf_botStoreSign
    {σ : Store} :
    σ ∈ gammaStoreOf gammaSign botStoreSign ↔ False := by
  constructor
  · intro hBot
    have hx : σ .x0 ∈ gammaSign (botStoreSign .x0) := hBot .x0
    simp [botStoreSign, gammaSign] at hx
  · intro hFalse
    exact False.elim hFalse

@[simp] theorem mem_gammaConfigOf_singletonConfigSign
    {target s : Stmt}
    {ρ : StoreSharp Sign}
    {σ : Store} :
    (s, σ) ∈ gammaConfigOf gammaSign (singletonConfigSign target ρ) ↔
      s = target ∧ σ ∈ gammaStoreOf gammaSign ρ := by
  by_cases hEq : s = target
  · subst hEq
    simp [singletonConfigSign]
  · constructor
    · intro hConf
      exfalso
      have hBot : σ ∈ gammaStoreOf gammaSign botStoreSign := by
        simpa [singletonConfigSign, hEq] using hConf
      exact (mem_gammaStoreOf_botStoreSign.mp hBot)
    · rintro ⟨hTarget, _⟩
      exact (hEq hTarget).elim

theorem mem_gammaConfigOf_liftSeqConfig
    {s s2 : Stmt}
    {κ : ConfigSharp Sign}
    {σ : Store}
    (hσ : (s, σ) ∈ gammaConfigOf gammaSign κ) :
    (.seq s s2, σ) ∈ gammaConfigOf gammaSign (liftSeqConfig s2 κ) := by
  simpa [liftSeqConfig] using hσ

theorem mem_gammaProgram_join_left
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp Sign}
    {c : Config}
    (hc : c ∈ gammaProgramSign program κ₁) :
    c ∈ gammaProgramSign program (joinConfigSign κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, impConfigSignDomain.join_sound κ₁ κ₂ (Or.inl hConf)⟩

theorem mem_gammaProgram_join_right
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp Sign}
    {c : Config}
    (hc : c ∈ gammaProgramSign program κ₂) :
    c ∈ gammaProgramSign program (joinConfigSign κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, impConfigSignDomain.join_sound κ₁ κ₂ (Or.inr hConf)⟩

theorem mem_gammaProgram_seqLeft
    {s1 s2 : Stmt}
    {κ : ConfigSharp Sign}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramSign s1 κ) :
    (Stmt.seq s s2, σ) ∈ gammaProgramSign (.seq s1 s2) (liftSeqConfig s2 κ) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqLeft hActive, mem_gammaConfigOf_liftSeqConfig hConf⟩

theorem mem_gammaProgram_seqRight
    {s1 s2 : Stmt}
    {κ : ConfigSharp Sign}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramSign s2 κ) :
    (s, σ) ∈ gammaProgramSign (.seq s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqRight hActive, hConf⟩

theorem mem_gammaProgram_iteThen
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp Sign}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramSign s1 κ) :
    (s, σ) ∈ gammaProgramSign (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteThen hActive, hConf⟩

theorem mem_gammaProgram_iteElse
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp Sign}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramSign s2 κ) :
    (s, σ) ∈ gammaProgramSign (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteElse hActive, hConf⟩

theorem evalSignExpr_sound
    {ρ : StoreSharp Sign}
    {σ : Store}
    {e : Expr}
    (hσ : σ ∈ gammaStoreOf gammaSign ρ) :
    eval σ e ∈ gammaSign (evalSignExpr ρ e) := by
  induction e with
  | lit n =>
      simpa [evalSignExpr] using constSign_sound n
  | var x =>
      simpa [evalSignExpr] using hσ x
  | add e1 e2 ih1 ih2 =>
      simpa [evalSignExpr, eval_add] using addTransfer_sound ih1 ih2

theorem mem_gammaStoreOf_updateStoreSharp
    {ρ : StoreSharp Sign}
    {σ : Store}
    {x : Var}
    {a : Sign}
    {v : Int}
    (hσ : σ ∈ gammaStoreOf gammaSign ρ)
    (hv : v ∈ gammaSign a) :
    σ.update x v ∈ gammaStoreOf gammaSign (updateStoreSharp ρ x a) := by
  intro y
  by_cases hEq : x = y
  · subst hEq
    simpa [Store.update, updateStoreSharp] using hv
  · simp [Store.update, updateStoreSharp, hEq, hσ y]

theorem mem_gammaStoreOf_assumeTrueStore
    {cond : Expr}
    {ρ : StoreSharp Sign}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf gammaSign ρ)
    (hCond : eval σ cond ≠ 0) :
    σ ∈ gammaStoreOf gammaSign (assumeTrueStore cond ρ) := by
  cases cond with
  | lit n =>
      have hNe : n ≠ 0 := by
        simpa using hCond
      simpa [assumeTrueStore, hNe] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeTrueStore, updateStoreSharp]
        exact assumeNonzero_sound (hσ x) hCond
      · simp [assumeTrueStore, updateStoreSharp, hEq, hσ y]
  | add =>
      simpa [assumeTrueStore] using hσ

theorem mem_gammaStoreOf_assumeFalseStore
    {cond : Expr}
    {ρ : StoreSharp Sign}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf gammaSign ρ)
    (hCond : eval σ cond = 0) :
    σ ∈ gammaStoreOf gammaSign (assumeFalseStore cond ρ) := by
  cases cond with
  | lit n =>
      have hZero : n = 0 := by
        simpa using hCond
      simpa [assumeFalseStore, hZero] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeFalseStore, updateStoreSharp]
        exact assumeZero_sound (hσ x) hCond
      · simp [assumeFalseStore, updateStoreSharp, hEq, hσ y]
  | add =>
      simpa [assumeFalseStore] using hσ

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
