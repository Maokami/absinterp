import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterpLTS.Domains
import AbsInterpLTS.Framework
import AbsInterpLTS.Instances.LTS
import Examples.IMP.Abstraction
import Examples.IMP.LTS
import Examples.IMP.Semantics

namespace Examples.IMP

open AbsInterpLTS
open AbsInterpLTS.Domains
open AbsInterpLTS.Framework
open AbsInterpLTS.Framework.Domains
open AbsInterpLTS.Instances.LTS

/-!
Definitions for the generic Sign analysis over the canonical IMP LTS.

This file contains the executable transfer machinery and abstract-state
shaping helpers. Proof-oriented lemmas live in `Lemmas.lean`, and the main
soundness induction lives in `Soundness.lean`.
-/

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

/-- Top abstract store for IMP Sign analysis. -/
def topStoreSign : StoreSharp Sign :=
  fun _ => .top

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

/-- Initial abstract configuration focused at a program entry point. -/
def initAt
    (program : Stmt)
    (ρ : StoreSharp Sign) :
    ConfigSharp Sign :=
  singletonConfigSign program ρ

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
  | .lit n => if n = 0 then botStoreSign else ρ
  | .var x => updateStoreSharp ρ x (assumeNonzero (ρ x))
  | _ => ρ

/-- Refine an abstract store under a not-taken `if` branch. -/
def assumeFalseStore
    (cond : Expr)
    (ρ : StoreSharp Sign) :
    StoreSharp Sign :=
  match cond with
  | .lit n => if n = 0 then ρ else botStoreSign
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

end Examples.IMP
