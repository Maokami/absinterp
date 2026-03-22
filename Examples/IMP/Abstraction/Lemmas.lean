import Cslib.Init

import Examples.IMP.Abstraction.Defs

namespace Examples.IMP

@[simp] theorem controlOfConfig_mk (s : Stmt) (σ : Store) :
    controlOfConfig (s, σ) = s :=
  rfl

@[simp] theorem storeOfConfig_mk (s : Stmt) (σ : Store) :
    storeOfConfig (s, σ) = σ :=
  rfl

@[simp] theorem mem_gammaStoreOf
    {Abstract : Type _}
    {gamma : Abstract → Set Int}
    {ρ : StoreSharp Abstract}
    {σ : Store} :
    σ ∈ gammaStoreOf gamma ρ ↔ ∀ x : Var, σ x ∈ gamma (ρ x) :=
  Iff.rfl

@[simp] theorem mem_gammaConfigOf_mk
    {Abstract : Type _}
    {gamma : Abstract → Set Int}
    {κ : ConfigSharp Abstract}
    {s : Stmt}
    {σ : Store} :
    (s, σ) ∈ gammaConfigOf gamma κ ↔
      σ ∈ gammaStoreOf gamma (κ s) :=
  Iff.rfl

end Examples.IMP
