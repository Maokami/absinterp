import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS
import Examples.IMP.Analysis.Common
import Examples.IMP.LTS
import Examples.IMP.Semantics.Lemmas

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

/-- Convenient alias for the lifted Sign config domain on IMP configurations. -/
abbrev impConfigSignDomain : GammaOnlyDomain (ConfigSharp Sign) Config :=
  configGammaOnlyDomain signGammaOnlyDomain

/-- The generic Sign concretization for a fixed IMP program. -/
def gammaProgramSign (program : Stmt) : AbsInterpLTS.Framework.Gamma (ConfigSharp Sign) Config :=
  gammaProgramConfigOf program gammaSign

/-- Bottom abstract store for IMP Sign analysis. -/
def botStoreSign : StoreSharp Sign :=
  fun _ => .bot

/-- Bottom abstract configuration for IMP Sign analysis. -/
def botConfigSign : ConfigSharp Sign :=
  fun _ => botStoreSign

@[simp] theorem botStoreSign_apply (x : Var) :
    botStoreSign x = .bot := rfl

@[simp] theorem botConfigSign_apply (s : Stmt) (x : Var) :
    botConfigSign s x = .bot := rfl

/-- Pointwise update of an abstract IMP store. -/
def updateStoreSharp
    (ρ : StoreSharp Sign)
    (x : Var)
    (a : Sign) :
    StoreSharp Sign :=
  fun y => if x = y then a else ρ y

@[simp] theorem updateStoreSharp_same
    (ρ : StoreSharp Sign)
    (x : Var)
    (a : Sign) :
    updateStoreSharp ρ x a x = a := by
  simp [updateStoreSharp]

@[simp] theorem updateStoreSharp_other
    (ρ : StoreSharp Sign)
    (x y : Var)
    (a : Sign)
    (hNe : x ≠ y) :
    updateStoreSharp ρ x a y = ρ y := by
  simp [updateStoreSharp, hNe]

/-- One-target abstract configuration contribution. -/
def singletonConfigSign
    (target : Stmt)
    (ρ : StoreSharp Sign) :
    ConfigSharp Sign :=
  fun s => if s = target then ρ else botStoreSign

/-- View the left phase of a sequence as a standalone abstract sub-configuration. -/
def seqView
    (s2 : Stmt)
    (κ : ConfigSharp Sign) :
    ConfigSharp Sign :=
  fun s => κ (.seq s s2)

/-- Re-attach a sequence suffix to every control location in an abstract sub-configuration. -/
def liftSeqConfig
    (s2 : Stmt)
    (κ : ConfigSharp Sign) :
    ConfigSharp Sign
  | .seq s s2' => if s2' = s2 then κ s else botStoreSign
  | _ => botStoreSign

/-- Join on IMP Sign abstract configurations. -/
def joinConfigSign
    (κ₁ κ₂ : ConfigSharp Sign) :
    ConfigSharp Sign :=
  impConfigSignDomain.join κ₁ κ₂

@[simp] theorem joinConfigSign_apply
    (κ₁ κ₂ : ConfigSharp Sign)
    (s : Stmt)
    (x : Var) :
    joinConfigSign κ₁ κ₂ s x = joinSign (κ₁ s x) (κ₂ s x) := rfl

/-- Abstract expression evaluation over Sign stores. -/
def evalSignExpr
    (ρ : StoreSharp Sign) : Expr → Sign
  | .lit n => constSign n
  | .var x => ρ x
  | .add e1 e2 => addTransfer (evalSignExpr ρ e1) (evalSignExpr ρ e2)

/-- Refine an abstract store under a taken `if` branch. -/
def assumeTrueStore
    (cond : Expr)
    (ρ : StoreSharp Sign) :
    StoreSharp Sign :=
  match cond with
  | .var x => updateStoreSharp ρ x (assumeNonzero (ρ x))
  | _ => ρ

/-- Refine an abstract store under a not-taken `if` branch. -/
def assumeFalseStore
    (cond : Expr)
    (ρ : StoreSharp Sign) :
    StoreSharp Sign :=
  match cond with
  | .var x => updateStoreSharp ρ x (assumeZero (ρ x))
  | _ => ρ

/--
Generic Sign transfer for the labeled IMP LTS, parameterized by the root program
whose active control closure is being analyzed.
-/
def transferProgramSign :
    Stmt → StepLabel → ConfigSharp Sign → ConfigSharp Sign
  | .skip, _, _ => botConfigSign
  | .assign x e, .assign, κ =>
      singletonConfigSign
        .skip
        (updateStoreSharp (κ (.assign x e)) x (evalSignExpr (κ (.assign x e)) e))
  | .assign _ _, _, _ => botConfigSign
  | .seq s1 s2, .seqStep μ, κ =>
      joinConfigSign
        (liftSeqConfig s2 (transferProgramSign s1 μ (seqView s2 κ)))
        (transferProgramSign s2 (.seqStep μ) κ)
  | .seq _ s2, .seqDone, κ =>
      joinConfigSign
        (singletonConfigSign s2 ((seqView s2 κ) .skip))
        (transferProgramSign s2 .seqDone κ)
  | .seq _ s2, μ, κ =>
      transferProgramSign s2 μ κ
  | .ite cond s1 s2, .ifTrue, κ =>
      joinConfigSign
        (singletonConfigSign s1 (assumeTrueStore cond (κ (.ite cond s1 s2))))
        (joinConfigSign
          (transferProgramSign s1 .ifTrue κ)
          (transferProgramSign s2 .ifTrue κ))
  | .ite cond s1 s2, .ifFalse, κ =>
      joinConfigSign
        (singletonConfigSign s2 (assumeFalseStore cond (κ (.ite cond s1 s2))))
        (joinConfigSign
          (transferProgramSign s1 .ifFalse κ)
          (transferProgramSign s2 .ifFalse κ))
  | .ite _ s1 s2, μ, κ =>
      joinConfigSign
        (transferProgramSign s1 μ κ)
        (transferProgramSign s2 μ κ)
termination_by program _ _ => program

/-- Package the generic Sign transfer as a framework step transformer. -/
def impSignTransfer
    (program : Stmt) :
    StepPostSharp (ConfigSharp Sign) StepLabel :=
  transferProgramSign program

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
  | lit =>
      simpa [assumeTrueStore] using hσ
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
  | lit =>
      simpa [assumeFalseStore] using hσ
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

/-! ## Smoke Examples -/

def assignFive : Stmt :=
  .assign .x0 (.lit 5)

def branchOnX0 : Stmt :=
  .ite (.var .x0) (.assign .x1 (.lit 1)) (.assign .x1 (.lit 0))

def topStoreSign : StoreSharp Sign :=
  fun _ => .top

def branchInitStore : StoreSharp Sign
  | .x0 => .nonneg
  | .x1 => .top

def initAt
    (program : Stmt)
    (ρ : StoreSharp Sign) :
    ConfigSharp Sign :=
  singletonConfigSign program ρ

example :
    (transferProgramSign assignFive .assign (initAt assignFive topStoreSign)) .skip .x0 = .pos := by
  simp [transferProgramSign, assignFive, initAt, singletonConfigSign,
    updateStoreSharp, evalSignExpr, constSign]

example :
    (transferProgramSign branchOnX0 .ifTrue (initAt branchOnX0 branchInitStore))
      (.assign .x1 (.lit 1)) .x0 = .pos := by
  simp [transferProgramSign, branchOnX0, initAt, singletonConfigSign, branchInitStore,
    assumeTrueStore, assumeNonzero, botConfigSign, botStoreSign]

example :
    (transferProgramSign branchOnX0 .ifFalse (initAt branchOnX0 branchInitStore))
      (.assign .x1 (.lit 0)) .x0 = .zero := by
  simp [transferProgramSign, branchOnX0, initAt, singletonConfigSign, branchInitStore,
    assumeFalseStore, assumeZero, botConfigSign, botStoreSign]

example :
    SoundTrace
      (liftTracePost (postStep impLTS))
      (gammaProgramSign branchOnX0)
      (liftTracePostSharp (impSignTransfer branchOnX0)) :=
  (impSignAbstraction branchOnX0).soundTraceLifted

end Examples.IMP
