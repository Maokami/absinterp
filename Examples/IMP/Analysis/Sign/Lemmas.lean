import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Domains
import AbsInterpLTS.Framework
import AbsInterpLTS.Instances.LTS
import Examples.IMP.Analysis.Sign.Defs

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

/-!
Helper lemmas for the generic IMP Sign analysis.

This file keeps concrete membership and refinement facts separate from the main
soundness induction.
-/

@[simp] theorem mem_gammaStoreOf_botStoreSign
    {σ : Store} :
    σ ∈ gammaStoreOf gammaSign botStoreSign ↔ False := by
  constructor
  · intro hBot
    have hx0 : σ .x0 ∈ gammaSign (botStoreSign .x0) := hBot .x0
    change σ .x0 ∈ (∅ : Set Int) at hx0
    rw [Set.mem_empty_iff_false] at hx0
    exact hx0
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

end Examples.IMP
