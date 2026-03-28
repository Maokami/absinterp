import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Domains
import Examples.IMP.Semantics

namespace Examples.IMP

open AbsInterp.Framework
open AbsInterp.Framework.Domains

universe u

/-- Control locations for textbook IMP configurations are just statements. -/
abbrev Control := Stmt

/-- Forget the store component of a concrete configuration. -/
def controlOfConfig : Config → Control
  | (s, _) => s

/-- Forget the control component of a concrete configuration. -/
def storeOfConfig : Config → Store
  | (_, σ) => σ

/-- Pointwise abstract store over the fixed IMP variable set. -/
abbrev StoreSharp (Abstract : Type u) := Var → Abstract

/-- Pointwise abstract configurations indexed by IMP control locations. -/
abbrev ConfigSharp (Abstract : Type u) := Control → StoreSharp Abstract

/-- Pointwise update of an abstract IMP store. -/
def updateStoreSharp
    {Abstract : Type u}
    (ρ : StoreSharp Abstract)
    (x : Var)
    (a : Abstract) :
    StoreSharp Abstract :=
  fun y => if x = y then a else ρ y

@[simp] theorem updateStoreSharp_same
    {Abstract : Type u}
    (ρ : StoreSharp Abstract)
    (x : Var)
    (a : Abstract) :
    updateStoreSharp ρ x a x = a := by
  simp [updateStoreSharp]

@[simp] theorem updateStoreSharp_other
    {Abstract : Type u}
    (ρ : StoreSharp Abstract)
    (x y : Var)
    (a : Abstract)
    (hNe : x ≠ y) :
    updateStoreSharp ρ x a y = ρ y := by
  simp [updateStoreSharp, hNe]

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

/-- Pointwise bottom element on abstract IMP stores. -/
def botStoreSharp
    {Abstract : Type u}
    [Bot Abstract] :
    StoreSharp Abstract :=
  fun _ => ⊥

@[simp] theorem botStoreSharp_apply
    {Abstract : Type u}
    [Bot Abstract]
    (x : Var) :
    botStoreSharp (Abstract := Abstract) x = (⊥ : Abstract) :=
  rfl

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
    intro ρ₁ ρ₂ σ hUnion x
    apply cfg.join_sound
    rcases hUnion with hLeft | hRight
    · exact Or.inl (hLeft x)
    · exact Or.inr (hRight x)

/-- Pointwise order on abstract IMP configurations. -/
def leConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract → ConfigSharp Abstract → Prop :=
  fun κ₁ κ₂ => ∀ s : Control, cfg.le (κ₁ s) (κ₂ s)

/-- Pointwise top element on abstract IMP configurations. -/
def topConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract :=
  fun _ => cfg.top

/-- Pointwise bottom element on abstract IMP configurations. -/
def botConfigSharp
    {Abstract : Type u}
    [Bot Abstract] :
    ConfigSharp Abstract :=
  fun _ => botStoreSharp

@[simp] theorem botConfigSharp_apply
    {Abstract : Type u}
    [Bot Abstract]
    (s : Stmt)
    (x : Var) :
    botConfigSharp (Abstract := Abstract) s x = (⊥ : Abstract) :=
  rfl

/-- Pointwise join on abstract IMP configurations. -/
def joinConfigSharp
    {Abstract : Type u}
    (cfg : GammaOnlyDomain (StoreSharp Abstract) Store) :
    ConfigSharp Abstract → ConfigSharp Abstract → ConfigSharp Abstract :=
  fun κ₁ κ₂ pc => cfg.join (κ₁ pc) (κ₂ pc)

/-- One-target abstract configuration contribution. -/
def singletonConfig
    {Abstract : Type u}
    [Bot Abstract]
    (target : Stmt)
    (ρ : StoreSharp Abstract) :
    ConfigSharp Abstract :=
  fun s => if s = target then ρ else botStoreSharp

/-- Initial abstract configuration focused at a program entry point. -/
def initAt
    {Abstract : Type u}
    [Bot Abstract]
    (program : Stmt)
    (ρ : StoreSharp Abstract) :
    ConfigSharp Abstract :=
  singletonConfig program ρ

/-- View the left phase of a sequence as a standalone abstract sub-configuration. -/
def seqView
    {Abstract : Type u}
    (s2 : Stmt)
    (κ : ConfigSharp Abstract) :
    ConfigSharp Abstract :=
  fun s => κ (.seq s s2)

/-- Re-attach a sequence suffix to every control location in an abstract sub-configuration. -/
def liftSeqConfig
    {Abstract : Type u}
    [Bot Abstract]
    (s2 : Stmt)
    (κ : ConfigSharp Abstract) :
    ConfigSharp Abstract
  | .seq s s2' => if s2' = s2 then κ s else botStoreSharp
  | _ => botStoreSharp

/-- Join on IMP abstract configurations lifted from a scalar domain. -/
def joinConfig
    {Abstract : Type u}
    (cfg : GammaOnlyDomain Abstract Int) :
    ConfigSharp Abstract → ConfigSharp Abstract → ConfigSharp Abstract :=
  joinConfigSharp (storeGammaOnlyDomain cfg)

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
      exact storeCfg.gamma_monotone (hLe (controlOfConfig c)) hc
    top := topConfigSharp storeCfg
    gamma_top := by
      intro c
      exact storeCfg.gamma_top (storeOfConfig c)
    join := joinConfigSharp storeCfg
    join_sound := by
      intro κ₁ κ₂ c hc
      change
        storeOfConfig c ∈ gammaStoreOf cfg.gamma (κ₁ (controlOfConfig c)) ∪
          gammaStoreOf cfg.gamma (κ₂ (controlOfConfig c)) at hc
      exact storeCfg.join_sound (κ₁ (controlOfConfig c)) (κ₂ (controlOfConfig c)) hc
  }

end Examples.IMP
