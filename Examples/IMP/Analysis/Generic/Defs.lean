import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework
import AbsInterp.Instances.LTS
import Examples.IMP.Abstraction
import Examples.IMP.LTS
import Examples.IMP.Semantics
import Examples.IMP.Analysis.Generic.Domain

namespace Examples.IMP

open AbsInterp
open AbsInterp.Framework
open AbsInterp.Framework.Domains
open AbsInterp.Instances.LTS

universe u

variable {A : Type u} [Bot A]

/-!
# Generic IMP Transfer Functions

Transfer machinery parameterized by `IMPAnalysisDomain`, covering expression
evaluation, branch refinement, and the full program transfer function.
-/

/-- Abstract expression evaluation parameterized by an IMP analysis domain. -/
def evalExpr (d : IMPAnalysisDomain A) (ρ : StoreSharp A) : Expr → A
  | .lit n => d.const n
  | .var x => ρ x
  | .add e1 e2 => d.addTransfer (evalExpr d ρ e1) (evalExpr d ρ e2)

/-- Refine variables in an abstract store using a backward-refined pair.
    Each sub-expression that is a variable gets its store entry updated. -/
def refineAddStore
    (ρ : StoreSharp A) (e1 e2 : Expr) (pair : A × A) : StoreSharp A :=
  let ρ' := match e1 with | .var x => updateStoreSharp ρ x pair.1 | _ => ρ
  match e2 with | .var y => updateStoreSharp ρ' y pair.2 | _ => ρ'

/-- Refine an abstract store under a taken `if` branch. -/
def assumeTrueStoreOf (d : IMPAnalysisDomain A) (cond : Expr)
    (ρ : StoreSharp A) : StoreSharp A :=
  match cond with
  | .lit n => if n = 0 then botStoreSharp else ρ
  | .var x => updateStoreSharp ρ x (d.assumeNonzero (ρ x))
  | .add e1 e2 =>
      refineAddStore ρ e1 e2 (d.assumeNonzeroAdd (evalExpr d ρ e1) (evalExpr d ρ e2))

/-- Refine an abstract store under a not-taken `if` branch. -/
def assumeFalseStoreOf (d : IMPAnalysisDomain A) (cond : Expr)
    (ρ : StoreSharp A) : StoreSharp A :=
  match cond with
  | .lit n => if n = 0 then ρ else botStoreSharp
  | .var x => updateStoreSharp ρ x (d.assumeZero (ρ x))
  | .add e1 e2 =>
      refineAddStore ρ e1 e2 (d.assumeZeroAdd (evalExpr d ρ e1) (evalExpr d ρ e2))

/--
Generic transfer for the labeled IMP LTS, parameterized by an IMP analysis
domain and the root program whose active control closure is being analyzed.
-/
def transferProgram (d : IMPAnalysisDomain A) :
    Stmt → StepLabel → ConfigSharp A → ConfigSharp A
  | .skip, _, _ => botConfigSharp
  | .assign x e, .assign, κ =>
      singletonConfig .skip
        (updateStoreSharp (κ (.assign x e)) x (evalExpr d (κ (.assign x e)) e))
  | .assign _ _, _, _ => botConfigSharp
  | .seq s1 s2, .seqStep μ, κ =>
      joinConfig d.scalarDomain
        (liftSeqConfig s2 (transferProgram d s1 μ (seqView s2 κ)))
        (transferProgram d s2 (.seqStep μ) κ)
  | .seq _ s2, .seqDone, κ =>
      joinConfig d.scalarDomain
        (singletonConfig s2 ((seqView s2 κ) .skip))
        (transferProgram d s2 .seqDone κ)
  | .seq _ s2, μ, κ =>
      transferProgram d s2 μ κ
  | .ite cond s1 s2, .ifTrue, κ =>
      joinConfig d.scalarDomain
        (singletonConfig s1 (assumeTrueStoreOf d cond (κ (.ite cond s1 s2))))
        (joinConfig d.scalarDomain
          (transferProgram d s1 .ifTrue κ)
          (transferProgram d s2 .ifTrue κ))
  | .ite cond s1 s2, .ifFalse, κ =>
      joinConfig d.scalarDomain
        (singletonConfig s2 (assumeFalseStoreOf d cond (κ (.ite cond s1 s2))))
        (joinConfig d.scalarDomain
          (transferProgram d s1 .ifFalse κ)
          (transferProgram d s2 .ifFalse κ))
  | .ite _ s1 s2, μ, κ =>
      joinConfig d.scalarDomain
        (transferProgram d s1 μ κ)
        (transferProgram d s2 μ κ)
  | .while cond body, .whileTrue, κ =>
      singletonConfig
        (.seq body (.while cond body))
        (assumeTrueStoreOf d cond (κ (.while cond body)))
  | .while cond body, .whileFalse, κ =>
      singletonConfig .skip
        (assumeFalseStoreOf d cond (κ (.while cond body)))
  | .while cond body, .seqStep μ, κ =>
      liftSeqConfig (.while cond body)
        (transferProgram d body μ (seqView (.while cond body) κ))
  | .while cond body, .seqDone, κ =>
      singletonConfig (.while cond body)
        ((seqView (.while cond body) κ) .skip)
  | .while _ _, _, _ => botConfigSharp
termination_by program _ _ => program

/-- The generic concretization for a fixed IMP program and domain. -/
def gammaProgram (d : IMPAnalysisDomain A) (program : Stmt) :
    AbsInterp.Framework.Gamma (ConfigSharp A) Config :=
  gammaProgramConfigOf program d.scalarDomain.gamma

/-- Package the generic transfer as a framework step transformer. -/
def impTransfer (d : IMPAnalysisDomain A) (program : Stmt) :
    StepPostSharp (ConfigSharp A) StepLabel :=
  transferProgram d program

end Examples.IMP
