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
Definitions for the generic Interval analysis over the canonical IMP LTS.

This file contains the executable transfer machinery and abstract-state
shaping helpers. Proof-oriented lemmas live in `Lemmas.lean`, and the main
soundness induction lives in `Soundness.lean`.
-/

/-- Convenient alias for the lifted Interval config domain on IMP configurations. -/
abbrev impConfigIntervalDomain : GammaOnlyDomain (ConfigSharp Interval) Config :=
  configGammaOnlyDomain intervalGammaOnlyDomain

/-- The generic Interval concretization for a fixed IMP program. -/
def gammaProgramInterval (program : Stmt) : AbsInterpLTS.Framework.Gamma (ConfigSharp Interval) Config :=
  gammaProgramConfigOf program gammaInterval

/-- Bottom abstract store for IMP Interval analysis. -/
abbrev botStoreInterval : StoreSharp Interval :=
  botStoreSharp

/-- Bottom abstract configuration for IMP Interval analysis. -/
abbrev botConfigInterval : ConfigSharp Interval :=
  botConfigSharp

/-- Top abstract store for IMP Interval analysis. -/
def topStoreInterval : StoreSharp Interval :=
  fun _ => .top

/-- One-target abstract configuration contribution. -/
abbrev singletonConfigInterval
    (target : Stmt)
    (ρ : StoreSharp Interval) :
    ConfigSharp Interval :=
  singletonConfig target ρ

/-- Join on IMP Interval abstract configurations. -/
abbrev joinConfigInterval
    (κ₁ κ₂ : ConfigSharp Interval) :
    ConfigSharp Interval :=
  joinConfig intervalGammaOnlyDomain κ₁ κ₂

@[simp] theorem joinConfigInterval_apply
    (κ₁ κ₂ : ConfigSharp Interval)
    (s : Stmt)
    (x : Var) :
    joinConfigInterval κ₁ κ₂ s x = joinInterval (κ₁ s x) (κ₂ s x) := rfl

/-- Abstract expression evaluation over Interval stores. -/
def evalIntervalExpr
    (ρ : StoreSharp Interval) : Expr → Interval
  | .lit n => constInterval n
  | .var x => ρ x
  | .add e1 e2 => addIntervalTransfer (evalIntervalExpr ρ e1) (evalIntervalExpr ρ e2)

/-- Refine an abstract store under a taken `if` branch. -/
def assumeTrueStoreInterval
    (cond : Expr)
    (ρ : StoreSharp Interval) :
    StoreSharp Interval :=
  match cond with
  | .lit n => if n = 0 then botStoreInterval else ρ
  | .var x => updateStoreSharp ρ x (assumeNonzeroInterval (ρ x))
  | _ => ρ

/-- Refine an abstract store under a not-taken `if` branch. -/
def assumeFalseStoreInterval
    (cond : Expr)
    (ρ : StoreSharp Interval) :
    StoreSharp Interval :=
  match cond with
  | .lit n => if n = 0 then ρ else botStoreInterval
  | .var x => updateStoreSharp ρ x (assumeZeroInterval (ρ x))
  | _ => ρ

/--
Generic Interval transfer for the labeled IMP LTS, parameterized by the root program
whose active control closure is being analyzed.
-/
def transferProgramInterval :
    Stmt → StepLabel → ConfigSharp Interval → ConfigSharp Interval
  | .skip, _, _ => botConfigInterval
  | .assign x e, .assign, κ =>
      singletonConfigInterval
        .skip
        (updateStoreSharp (κ (.assign x e)) x (evalIntervalExpr (κ (.assign x e)) e))
  | .assign _ _, _, _ => botConfigInterval
  | .seq s1 s2, .seqStep μ, κ =>
      joinConfigInterval
        (liftSeqConfig s2 (transferProgramInterval s1 μ (seqView s2 κ)))
        (transferProgramInterval s2 (.seqStep μ) κ)
  | .seq _ s2, .seqDone, κ =>
      joinConfigInterval
        (singletonConfigInterval s2 ((seqView s2 κ) .skip))
        (transferProgramInterval s2 .seqDone κ)
  | .seq _ s2, μ, κ =>
      transferProgramInterval s2 μ κ
  | .ite cond s1 s2, .ifTrue, κ =>
      joinConfigInterval
        (singletonConfigInterval s1 (assumeTrueStoreInterval cond (κ (.ite cond s1 s2))))
        (joinConfigInterval
          (transferProgramInterval s1 .ifTrue κ)
          (transferProgramInterval s2 .ifTrue κ))
  | .ite cond s1 s2, .ifFalse, κ =>
      joinConfigInterval
        (singletonConfigInterval s2 (assumeFalseStoreInterval cond (κ (.ite cond s1 s2))))
        (joinConfigInterval
          (transferProgramInterval s1 .ifFalse κ)
          (transferProgramInterval s2 .ifFalse κ))
  | .ite _ s1 s2, μ, κ =>
      joinConfigInterval
        (transferProgramInterval s1 μ κ)
        (transferProgramInterval s2 μ κ)
termination_by program _ _ => program

/-- Package the generic Interval transfer as a framework step transformer. -/
def impIntervalTransfer
    (program : Stmt) :
    StepPostSharp (ConfigSharp Interval) StepLabel :=
  transferProgramInterval program

end Examples.IMP
