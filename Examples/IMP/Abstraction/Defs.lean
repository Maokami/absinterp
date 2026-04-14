import Cslib.Init
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

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

/--
Pointwise bottom element on abstract IMP stores.

Bottom is an opt-in requirement (`[Bot Abstract]`); it is not carried by
`GammaOnlyDomain` itself but is needed for "unreachable control location"
configurations like `singletonConfig`.
-/
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

/-!
## Pointwise lifts of `GammaOnlyDomain`

The Mathlib `Pi` instances (`Pi.preorder`, `Pi.instOrderTop`, `Pi.instMax`)
give us `≤`, `⊤`, and `⊔` on `Var → Abstract` and `Stmt → Var → Abstract`
automatically, so the lifted domain only has to supply the γ-level
soundness obligations.
-/

/-- Pointwise IMP-store domain lifted from a scalar integer domain. -/
def storeGammaOnlyDomain
    {Abstract : Type u}
    [Preorder Abstract] [OrderTop Abstract] [Max Abstract]
    (cfg : GammaOnlyDomain Abstract Int) :
    GammaOnlyDomain (StoreSharp Abstract) Store where
  gamma := gammaStoreOf cfg.gamma
  gamma_monotone := by
    intro ρ₁ ρ₂ hLe σ hσ x
    exact cfg.gamma_monotone (hLe x) (hσ x)
  gamma_top := by
    intro σ x
    exact cfg.gamma_top (σ x)
  join_sound := by
    intro ρ₁ ρ₂ σ hUnion x
    apply cfg.join_sound
    rcases hUnion with hLeft | hRight
    · exact Or.inl (hLeft x)
    · exact Or.inr (hRight x)

/-- Pointwise IMP-configuration domain lifted from a scalar integer domain. -/
def configGammaOnlyDomain
    {Abstract : Type u}
    [Preorder Abstract] [OrderTop Abstract] [Max Abstract]
    (cfg : GammaOnlyDomain Abstract Int) :
    GammaOnlyDomain (ConfigSharp Abstract) Config where
  gamma := gammaConfigOf cfg.gamma
  gamma_monotone := by
    intro κ₁ κ₂ hLe c hc
    exact (storeGammaOnlyDomain cfg).gamma_monotone (hLe (controlOfConfig c)) hc
  gamma_top := by
    intro c
    exact (storeGammaOnlyDomain cfg).gamma_top (storeOfConfig c)
  join_sound := by
    intro κ₁ κ₂ c hc
    change
      storeOfConfig c ∈ gammaStoreOf cfg.gamma (κ₁ (controlOfConfig c)) ∪
        gammaStoreOf cfg.gamma (κ₂ (controlOfConfig c)) at hc
    exact (storeGammaOnlyDomain cfg).join_sound
      (κ₁ (controlOfConfig c)) (κ₂ (controlOfConfig c)) hc

/--
Pointwise join on abstract IMP configurations.

Retained as a named alias so that `Generic/Defs.lean` and
`Generic/Soundness.lean` can refer to `joinConfig d.scalarDomain` without
caring about the underlying `Pi`-instance `⊔`. The `cfg` argument is
intentionally unused beyond helping type inference.
-/
def joinConfig
    {Abstract : Type u}
    [Preorder Abstract] [OrderTop Abstract] [Max Abstract]
    (_cfg : GammaOnlyDomain Abstract Int) :
    ConfigSharp Abstract → ConfigSharp Abstract → ConfigSharp Abstract :=
  fun κ₁ κ₂ pc x => κ₁ pc x ⊔ κ₂ pc x

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

end Examples.IMP
