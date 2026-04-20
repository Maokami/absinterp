import Mathlib.Order.Basic

import AbsInterp.Framework.Concretization

namespace AbsInterp
namespace Framework
namespace Domains

universe u v

/-!
# Transfer Capabilities

Bundled abstract transformers and generic monotonicity predicates. These sit
between the semantic kernel and language-specific analysis adapters.
-/

/-- Soundness of a unary abstract transfer for a concrete operation `op`. -/
def SoundUnaryTransfer
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (op : Concrete → Concrete)
    (transfer : Abstract → Abstract) : Prop :=
  ∀ {a : Abstract} {c : Concrete},
    c ∈ gamma a → op c ∈ gamma (transfer a)

/-- Bundled sound unary transfer for a concrete operation `op`. -/
structure UnaryTransfer
    (Abstract : Type u)
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (op : Concrete → Concrete) where
  transfer : Abstract → Abstract
  sound : SoundUnaryTransfer gamma op transfer

instance
    {Abstract : Type u}
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {op : Concrete → Concrete} :
    CoeFun (UnaryTransfer Abstract (gamma := gamma) op)
      (fun _ => Abstract → Abstract) where
  coe transfer := transfer.transfer

/-- Soundness of a binary abstract transfer for a concrete operation `op`. -/
def SoundBinaryTransfer
    {Abstract : Type u} {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (op : Concrete → Concrete → Concrete)
    (transfer : Abstract → Abstract → Abstract) : Prop :=
  ∀ {a₁ a₂ : Abstract} {c₁ c₂ : Concrete},
    c₁ ∈ gamma a₁ → c₂ ∈ gamma a₂ → op c₁ c₂ ∈ gamma (transfer a₁ a₂)

/-- Bundled sound binary transfer for a concrete operation `op`. -/
structure BinaryTransfer
    (Abstract : Type u)
    {Concrete : Type v}
    (gamma : Concretization Abstract Concrete)
    (op : Concrete → Concrete → Concrete) where
  transfer : Abstract → Abstract → Abstract
  sound : SoundBinaryTransfer gamma op transfer

instance
    {Abstract : Type u}
    {Concrete : Type v}
    {gamma : Concretization Abstract Concrete}
    {op : Concrete → Concrete → Concrete} :
    CoeFun (BinaryTransfer Abstract (gamma := gamma) op)
      (fun _ => Abstract → Abstract → Abstract) where
  coe transfer := transfer.transfer

/-- Monotonicity of a unary abstract transformer. -/
def MonotoneUnaryTransfer
    {Abstract : Type u} [Preorder Abstract]
    (transfer : Abstract → Abstract) : Prop :=
  ∀ {a b : Abstract}, a ≤ b → transfer a ≤ transfer b

/-- Monotonicity of a binary abstract transformer in both arguments. -/
def MonotoneBinaryTransfer
    {Abstract : Type u} [Preorder Abstract]
    (transfer : Abstract → Abstract → Abstract) : Prop :=
  ∀ {a₁ b₁ a₂ b₂ : Abstract},
    a₁ ≤ b₁ → a₂ ≤ b₂ → transfer a₁ a₂ ≤ transfer b₁ b₂

end Domains
end Framework
end AbsInterp
