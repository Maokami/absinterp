import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Framework.Domains
import Examples.IMP.Semantics.Defs

namespace Examples.IMP

open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains

universe u

/-- Control locations for IMP configurations, forgetting concrete stores. -/
inductive Control where
  | running (s : Stmt)
  | done
  deriving DecidableEq, Repr

/-- Forget the store component of a concrete configuration. -/
def controlOfConfig : Config → Control
  | .running s _ => .running s
  | .done _ => .done

/-- Forget the control component of a concrete configuration. -/
def storeOfConfig : Config → Store
  | .running _ σ => σ
  | .done σ => σ

/-- Pointwise abstract store over the fixed IMP variable set. -/
abbrev StoreSharp (Abstract : Type u) := Var → Abstract

/-- Pointwise abstract configurations indexed by IMP control locations. -/
abbrev ConfigSharp (Abstract : Type u) := Control → StoreSharp Abstract

/-- Lift a scalar concretization to IMP stores pointwise. -/
def gammaStoreOf
    {Abstract : Type u}
    (gamma : Abstract → Set Int) :
    Gamma (StoreSharp Abstract) Store :=
  fun ρ => { σ : Store | ∀ x : Var, σ x ∈ gamma (ρ x) }

/-- Lift a scalar concretization to IMP configurations via control-indexed stores. -/
def gammaConfigOf
    {Abstract : Type u}
    (gamma : Abstract → Set Int) :
    Gamma (ConfigSharp Abstract) Config :=
  fun κ => { c : Config | storeOfConfig c ∈ gammaStoreOf gamma (κ (controlOfConfig c)) }

/-- Pointwise order on abstract IMP stores. -/
def leStoreSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    StoreSharp Abstract → StoreSharp Abstract → Prop :=
  fun ρ₁ ρ₂ => ∀ x : Var, cfg.le (ρ₁ x) (ρ₂ x)

/-- Pointwise top element on abstract IMP stores. -/
def topStoreSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    StoreSharp Abstract :=
  fun _ => cfg.top

/-- Pointwise join on abstract IMP stores. -/
def joinStoreSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    StoreSharp Abstract → StoreSharp Abstract → StoreSharp Abstract :=
  fun ρ₁ ρ₂ x => cfg.join (ρ₁ x) (ρ₂ x)

/-- Pointwise IMP-store domain lifted from a scalar integer domain. -/
def storeGammaOnlyDomain
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    GammaOnlyDomain (StoreSharp Abstract) Store where
  gamma := gammaStoreOf cfg.gamma
  le := leStoreSharp cfg
  le_refl := by
    intro ρ x
    exact cfg.le_refl (ρ x)
  le_trans := by
    intro ρ₁ ρ₂ ρ₃ h12 h23 x
    exact cfg.le_trans (h12 x) (h23 x)
  gamma_monotone := by
    intro ρ₁ ρ₂ hLe σ hσ x
    exact cfg.gamma_monotone (hLe x) (hσ x)
  top := topStoreSharp cfg
  gamma_top := by
    intro σ x
    exact cfg.gamma_top (σ x)
  join := joinStoreSharp cfg
  join_sound := by
    intro ρ₁ ρ₂ σ hσ x
    rcases hσ with hσ | hσ
    · exact cfg.join_sound (ρ₁ x) (ρ₂ x) (Or.inl (hσ x))
    · exact cfg.join_sound (ρ₁ x) (ρ₂ x) (Or.inr (hσ x))

/-- Pointwise order on abstract IMP configurations. -/
def leConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract → ConfigSharp Abstract → Prop :=
  fun κ₁ κ₂ => ∀ pc : Control, cfg.le (κ₁ pc) (κ₂ pc)

/-- Pointwise top element on abstract IMP configurations. -/
def topConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract :=
  fun _ => cfg.top

/-- Pointwise join on abstract IMP configurations. -/
def joinConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract → ConfigSharp Abstract → ConfigSharp Abstract :=
  fun κ₁ κ₂ pc => cfg.join (κ₁ pc) (κ₂ pc)

/-- Pointwise IMP-configuration domain lifted from a scalar integer domain. -/
def configGammaOnlyDomain
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    GammaOnlyDomain (ConfigSharp Abstract) Config :=
  let storeCfg := storeGammaOnlyDomain cfg
  {
    gamma := gammaConfigOf cfg.gamma
    le := leConfigSharp storeCfg
    le_refl := by
      intro κ pc
      exact storeCfg.le_refl (κ pc)
    le_trans := by
      intro κ₁ κ₂ κ₃ h12 h23 pc
      exact storeCfg.le_trans (h12 pc) (h23 pc)
    gamma_monotone := by
      intro κ₁ κ₂ hLe c hc
      cases c with
      | running s σ =>
          exact storeCfg.gamma_monotone (hLe (.running s)) hc
      | done σ =>
          exact storeCfg.gamma_monotone (hLe .done) hc
    top := topConfigSharp storeCfg
    gamma_top := by
      intro c
      cases c with
      | running s σ =>
          exact storeCfg.gamma_top σ
      | done σ =>
          exact storeCfg.gamma_top σ
    join := joinConfigSharp storeCfg
    join_sound := by
      intro κ₁ κ₂ c hc
      cases c with
      | running s σ =>
          exact storeCfg.join_sound (κ₁ (.running s)) (κ₂ (.running s)) hc
      | done σ =>
          exact storeCfg.join_sound (κ₁ .done) (κ₂ .done) hc
  }

end Examples.IMP
