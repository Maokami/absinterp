import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework
import AbsInterp.Instances.LTS
import Examples.IMP.Analysis.Generic.Defs

namespace Examples.IMP

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Instances.LTS

universe u

variable {A : Type u} [Bot A] (d : IMPAnalysisDomain A)

/-!
# Generic IMP Analysis Lemmas

Helper lemmas for the generic IMP analysis, parameterized by `IMPAnalysisDomain`.
These generalize the previously duplicated Sign and Interval lemma files.
-/

/-- Convenient alias for the lifted config domain. -/
abbrev impConfigDomain (d : IMPAnalysisDomain A) : GammaOnlyDomain (ConfigSharp A) Config :=
  configGammaOnlyDomain d.scalarDomain

@[simp] theorem mem_gammaStoreOf_botStoreSharp_of
    {σ : Store} :
    σ ∈ gammaStoreOf d.scalarDomain.gamma botStoreSharp ↔ False := by
  constructor
  · intro hBot
    have hx0 : σ Var.x0 ∈ d.scalarDomain.gamma (botStoreSharp Var.x0) := hBot Var.x0
    simp [botStoreSharp, d.gamma_bot] at hx0
  · exact False.elim

@[simp] theorem mem_gammaConfigOf_singletonConfig_of
    {target s : Stmt}
    {ρ : StoreSharp A}
    {σ : Store} :
    (s, σ) ∈ gammaConfigOf d.scalarDomain.gamma (singletonConfig target ρ) ↔
      s = target ∧ σ ∈ gammaStoreOf d.scalarDomain.gamma ρ := by
  by_cases hEq : s = target
  · subst hEq
    simp [singletonConfig]
  · constructor
    · intro hConf
      exfalso
      have hBot : σ ∈ gammaStoreOf d.scalarDomain.gamma botStoreSharp := by
        simpa [singletonConfig, hEq] using hConf
      exact ((mem_gammaStoreOf_botStoreSharp_of d).mp hBot)
    · rintro ⟨hTarget, _⟩
      exact (hEq hTarget).elim

theorem mem_gammaConfigOf_liftSeqConfig_of
    {s s2 : Stmt}
    {κ : ConfigSharp A}
    {σ : Store}
    (hσ : (s, σ) ∈ gammaConfigOf d.scalarDomain.gamma κ) :
    (.seq s s2, σ) ∈ gammaConfigOf d.scalarDomain.gamma (liftSeqConfig s2 κ) := by
  simpa [liftSeqConfig] using hσ

theorem mem_gammaProgram_join_left_of
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp A}
    {c : Config}
    (hc : c ∈ gammaProgram d program κ₁) :
    c ∈ gammaProgram d program (joinConfig d.scalarDomain κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, (impConfigDomain d).join_sound κ₁ κ₂ (Or.inl hConf)⟩

theorem mem_gammaProgram_join_right_of
    {program : Stmt}
    {κ₁ κ₂ : ConfigSharp A}
    {c : Config}
    (hc : c ∈ gammaProgram d program κ₂) :
    c ∈ gammaProgram d program (joinConfig d.scalarDomain κ₁ κ₂) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨hActive, (impConfigDomain d).join_sound κ₁ κ₂ (Or.inr hConf)⟩

theorem mem_gammaProgram_seqLeft_of
    {s1 s2 : Stmt}
    {κ : ConfigSharp A}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgram d s1 κ) :
    (Stmt.seq s s2, σ) ∈ gammaProgram d (.seq s1 s2) (liftSeqConfig s2 κ) := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqLeft hActive, mem_gammaConfigOf_liftSeqConfig_of d hConf⟩

theorem mem_gammaProgram_seqRight_of
    {s1 s2 : Stmt}
    {κ : ConfigSharp A}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgram d s2 κ) :
    (s, σ) ∈ gammaProgram d (.seq s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.seqRight hActive, hConf⟩

theorem mem_gammaProgram_iteThen_of
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp A}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgram d s1 κ) :
    (s, σ) ∈ gammaProgram d (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteThen hActive, hConf⟩

theorem mem_gammaProgram_iteElse_of
    {cond : Expr}
    {s1 s2 : Stmt}
    {κ : ConfigSharp A}
    {s : Stmt}
    {σ : Store}
    (hc : (s, σ) ∈ gammaProgram d s2 κ) :
    (s, σ) ∈ gammaProgram d (.ite cond s1 s2) κ := by
  rcases hc with ⟨hActive, hConf⟩
  exact ⟨ActiveIn.iteElse hActive, hConf⟩

theorem evalExpr_sound
    {ρ : StoreSharp A}
    {σ : Store}
    {e : Expr}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ) :
    eval σ e ∈ d.scalarDomain.gamma (evalExpr d ρ e) := by
  induction e with
  | lit n =>
      simpa [evalExpr] using d.const_sound n
  | var x =>
      simpa [evalExpr] using hσ x
  | add e1 e2 ih1 ih2 =>
      simpa [evalExpr, eval_add] using d.addTransfer_sound ih1 ih2

theorem mem_gammaStoreOf_updateStoreSharp_of
    {ρ : StoreSharp A}
    {σ : Store}
    {x : Var}
    {a : A}
    {v : Int}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ)
    (hv : v ∈ d.scalarDomain.gamma a) :
    σ.update x v ∈ gammaStoreOf d.scalarDomain.gamma (updateStoreSharp ρ x a) := by
  intro y
  by_cases hEq : x = y
  · subst hEq
    simpa [Store.update, updateStoreSharp] using hv
  · simp [Store.update, updateStoreSharp, hEq, hσ y]

/-- Backward refinement of a single variable in an abstract store is sound.
    If `σ ∈ γ(ρ)` and `σ(x) ∈ γ(a)`, then `σ ∈ γ(ρ[x ↦ a])`. -/
theorem mem_gammaStoreOf_refineVar
    {ρ : StoreSharp A}
    {σ : Store}
    {x : Var}
    {a : A}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ)
    (hx : σ x ∈ d.scalarDomain.gamma a) :
    σ ∈ gammaStoreOf d.scalarDomain.gamma (updateStoreSharp ρ x a) := by
  intro y
  by_cases hEq : x = y
  · subst hEq; simp [updateStoreSharp]; exact hx
  · simp [updateStoreSharp, hEq]; exact hσ y

theorem mem_gammaStoreOf_refineAddStore
    {ρ : StoreSharp A}
    {σ : Store}
    {e1 e2 : Expr}
    {pair : A × A}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ)
    (h1 : eval σ e1 ∈ d.scalarDomain.gamma pair.1)
    (h2 : eval σ e2 ∈ d.scalarDomain.gamma pair.2) :
    σ ∈ gammaStoreOf d.scalarDomain.gamma (refineAddStore ρ e1 e2 pair) := by
  cases e1 with
  | var x =>
      simp only [refineAddStore]
      cases e2 with
      | var y =>
          exact mem_gammaStoreOf_refineVar d (mem_gammaStoreOf_refineVar d hσ h1) h2
      | _ => exact mem_gammaStoreOf_refineVar d hσ h1
  | _ =>
      simp only [refineAddStore]
      cases e2 with
      | var y => exact mem_gammaStoreOf_refineVar d hσ h2
      | _ => exact hσ

theorem mem_gammaStoreOf_assumeTrueStoreOf
    {cond : Expr}
    {ρ : StoreSharp A}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ)
    (hCond : eval σ cond ≠ 0) :
    σ ∈ gammaStoreOf d.scalarDomain.gamma (assumeTrueStoreOf d cond ρ) := by
  cases cond with
  | lit n =>
      have hNe : n ≠ 0 := by simpa using hCond
      simpa [assumeTrueStoreOf, hNe] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeTrueStoreOf, updateStoreSharp]
        exact d.assumeNonzero_sound (hσ x) hCond
      · simp [assumeTrueStoreOf, updateStoreSharp, hEq, hσ y]
  | add e1 e2 =>
      simp only [assumeTrueStoreOf]
      have hPair := d.assumeNonzeroAdd_sound
        (evalExpr_sound d hσ (e := e1)) (evalExpr_sound d hσ (e := e2))
        (by simpa [eval] using hCond)
      exact mem_gammaStoreOf_refineAddStore d hσ hPair.1 hPair.2

theorem mem_gammaStoreOf_assumeFalseStoreOf
    {cond : Expr}
    {ρ : StoreSharp A}
    {σ : Store}
    (hσ : σ ∈ gammaStoreOf d.scalarDomain.gamma ρ)
    (hCond : eval σ cond = 0) :
    σ ∈ gammaStoreOf d.scalarDomain.gamma (assumeFalseStoreOf d cond ρ) := by
  cases cond with
  | lit n =>
      have hZero : n = 0 := by simpa using hCond
      simpa [assumeFalseStoreOf, hZero] using hσ
  | var x =>
      intro y
      by_cases hEq : x = y
      · subst hEq
        simp [assumeFalseStoreOf, updateStoreSharp]
        exact d.assumeZero_sound (hσ x) hCond
      · simp [assumeFalseStoreOf, updateStoreSharp, hEq, hσ y]
  | add e1 e2 =>
      simp only [assumeFalseStoreOf]
      have hPair := d.assumeZeroAdd_sound
        (evalExpr_sound d hσ (e := e1)) (evalExpr_sound d hσ (e := e2))
        (by simpa [eval] using hCond)
      exact mem_gammaStoreOf_refineAddStore d hσ hPair.1 hPair.2

end Examples.IMP
