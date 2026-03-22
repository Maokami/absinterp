import Cslib.Init

import Examples.IMP.Abstraction.Defs

namespace Examples.IMP

@[simp] theorem controlOfConfig_running (s : Stmt) (σ : Store) :
    controlOfConfig (.running s σ) = .running s :=
  rfl

@[simp] theorem controlOfConfig_done (σ : Store) :
    controlOfConfig (.done σ) = .done :=
  rfl

@[simp] theorem storeOfConfig_running (s : Stmt) (σ : Store) :
    storeOfConfig (.running s σ) = σ :=
  rfl

@[simp] theorem storeOfConfig_done (σ : Store) :
    storeOfConfig (.done σ) = σ :=
  rfl

@[simp] theorem mem_gammaStoreOf
    {Abstract : Type _}
    {gamma : Abstract → Set Int}
    {ρ : StoreSharp Abstract}
    {σ : Store} :
    σ ∈ gammaStoreOf gamma ρ ↔ ∀ x : Var, σ x ∈ gamma (ρ x) :=
  Iff.rfl

@[simp] theorem mem_gammaConfigOf_running
    {Abstract : Type _}
    {gamma : Abstract → Set Int}
    {κ : ConfigSharp Abstract}
    {s : Stmt}
    {σ : Store} :
    (.running s σ) ∈ gammaConfigOf gamma κ ↔
      σ ∈ gammaStoreOf gamma (κ (.running s)) :=
  Iff.rfl

@[simp] theorem mem_gammaConfigOf_done
    {Abstract : Type _}
    {gamma : Abstract → Set Int}
    {κ : ConfigSharp Abstract}
    {σ : Store} :
    (.done σ) ∈ gammaConfigOf gamma κ ↔
      σ ∈ gammaStoreOf gamma (κ .done) :=
  Iff.rfl

end Examples.IMP
