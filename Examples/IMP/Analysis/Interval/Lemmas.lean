import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Domains
import AbsInterpLTS.Framework
import AbsInterpLTS.Instances.LTS
import Examples.IMP.Analysis.Interval.Defs

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

/-!
Helper lemmas for the generic IMP Interval analysis.

This file keeps concrete membership and refinement facts separate from the main
soundness induction.
-/

@[simp] theorem mem_gammaStoreOf_botStoreInterval
    {σ : Store} :
    σ ∈ gammaStoreOf gammaInterval botStoreInterval ↔ False := by
  constructor
  · intro hBot
    have hx0 : σ .x0 ∈ gammaInterval (botStoreInterval .x0) := hBot .x0
    change σ .x0 ∈ (∅ : Set Int) at hx0
    rw [Set.mem_empty_iff_false] at hx0
    exact hx0
  · intro hFalse
    exact False.elim hFalse

@[simp] theorem mem_gammaConfigOf_singletonConfigInterval
    {target s : Stmt}
    {ρ : StoreSharp Interval}
    {σ : Store} :
    (s, σ) ∈ gammaConfigOf gammaInterval (singletonConfigInterval target ρ) ↔
      s = target ∧ σ ∈ gammaStoreOf gammaInterval ρ := by
  by_cases hEq : s = target
  · subst hEq
    simp [singletonConfigInterval, singletonConfig]
  · constructor
    · intro hConf
      exfalso
      have hBot : σ ∈ gammaStoreOf gammaInterval botStoreInterval := by
        simpa [singletonConfigInterval, singletonConfig, hEq] using hConf
      exact (mem_gammaStoreOf_botStoreInterval.mp hBot)
    · rintro ⟨hTarget, _⟩
      exact (hEq hTarget).elim

theorem mem_gammaConfigOf_liftSeqConfigInterval
    {s s2 : Stmt}
    {κ : ConfigSharp Interval}
    {σ : Store}
    (hσ : (s, σ) ∈ gammaConfigOf gammaInterval κ) :
    (.seq s s2, σ) ∈ gammaConfigOf gammaInterval (liftSeqConfig s2 κ) := by
  simpa [liftSeqConfig] using hσ

theorem mem_gammaProgram_join_left_interval
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp Interval}
    {c : Config}
    (hc : c ∈ gammaProgramInterval program κ₁) :
    c ∈ gammaProgramInterval program (joinConfigInterval κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, impConfigIntervalDomain.join_sound κ₁ κ₂ (Or.inl hConf)⟩

theorem mem_gammaProgram_join_right_interval
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp Interval}
    {c : Config}
    (hc : c ∈ gammaProgramInterval program κ₂) :
    c ∈ gammaProgramInterval program (joinConfigInterval κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, impConfigIntervalDomain.join_sound κ₁ κ₂ (Or.inr hConf)⟩

theorem mem_gammaProgram_seqLeft_interval
    {s1 s2 : Stmt}
    {κ : ConfigSharp Interval}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramInterval s1 κ) :
    (Stmt.seq s s2, σ) ∈ gammaProgramInterval (.seq s1 s2) (liftSeqConfig s2 κ) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqLeft hActive, mem_gammaConfigOf_liftSeqConfigInterval hConf⟩

theorem mem_gammaProgram_seqRight_interval
    {s1 s2 : Stmt}
    {κ : ConfigSharp Interval}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramInterval s2 κ) :
    (s, σ) ∈ gammaProgramInterval (.seq s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqRight hActive, hConf⟩

theorem mem_gammaProgram_iteThen_interval
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp Interval}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramInterval s1 κ) :
    (s, σ) ∈ gammaProgramInterval (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteThen hActive, hConf⟩

theorem mem_gammaProgram_iteElse_interval
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp Interval}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgramInterval s2 κ) :
    (s, σ) ∈ gammaProgramInterval (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteElse hActive, hConf⟩

theorem evalIntervalExpr_sound
    {ρ : StoreSharp Interval}
    {σ : Store}
    {e : Expr}
    (hσ : σ ∈ gammaStoreOf gammaInterval ρ) :
    eval σ e ∈ gammaInterval (evalIntervalExpr ρ e) := by
  induction e with
  | lit n =>
      simpa [evalIntervalExpr] using constInterval_sound n
  | var x =>
      simpa [evalIntervalExpr] using hσ x
  | add e1 e2 ih1 ih2 =>
      simpa [evalIntervalExpr, eval_add] using addIntervalTransfer_sound ih1 ih2

theorem mem_gammaStoreOf_updateStoreSharp_interval
    {ρ : StoreSharp Interval}
    {σ : Store}
    {x : Var}
    {a : Interval}
    {v : Int}
    (hσ : σ ∈ gammaStoreOf gammaInterval ρ)
    (hv : v ∈ gammaInterval a) :
    σ.update x v ∈ gammaStoreOf gammaInterval (updateStoreSharp ρ x a) := by
  intro y
  by_cases hEq : x = y
  · subst hEq
    simpa [Store.update, updateStoreSharp] using hv
  · simp [Store.update, updateStoreSharp, hEq, hσ y]

theorem mem_gammaStoreOf_assumeTrueStoreInterval
    {cond : Expr}
    {ρ : StoreSharp Interval}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf gammaInterval ρ)
    (hCond : eval σ cond ≠ 0) :
    σ ∈ gammaStoreOf gammaInterval (assumeTrueStoreInterval cond ρ) := by
  cases cond with
  | lit n =>
      have hNe : n ≠ 0 := by
        simpa using hCond
      simpa [assumeTrueStoreInterval, hNe] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeTrueStoreInterval, updateStoreSharp]
        exact assumeNonzeroInterval_sound (hσ x) hCond
      · simp [assumeTrueStoreInterval, updateStoreSharp, hEq, hσ y]
  | add =>
      simpa [assumeTrueStoreInterval] using hσ

theorem mem_gammaStoreOf_assumeFalseStoreInterval
    {cond : Expr}
    {ρ : StoreSharp Interval}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf gammaInterval ρ)
    (hCond : eval σ cond = 0) :
    σ ∈ gammaStoreOf gammaInterval (assumeFalseStoreInterval cond ρ) := by
  cases cond with
  | lit n =>
      have hZero : n = 0 := by
        simpa using hCond
      simpa [assumeFalseStoreInterval, hZero] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeFalseStoreInterval, updateStoreSharp]
        exact assumeZeroInterval_sound (hσ x) hCond
      · simp [assumeFalseStoreInterval, updateStoreSharp, hEq, hσ y]
  | add =>
      simpa [assumeFalseStoreInterval] using hσ

end Examples.IMP
