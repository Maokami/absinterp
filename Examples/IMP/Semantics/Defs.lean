import Cslib.Init

import Examples.IMP.Syntax

namespace Examples.IMP

/-- A store maps each variable to an integer value. -/
abbrev Store := Var → Int

/-- Update a store at variable `x` with value `v`. -/
def Store.update (σ : Store) (x : Var) (v : Int) : Store :=
  fun y => if x = y then v else σ y

/-- Evaluate an arithmetic expression in a store. -/
def eval (σ : Store) : Expr → Int
  | .lit n => n
  | .var x => σ x
  | .add e1 e2 => eval σ e1 + eval σ e2

/-- IMP configurations pair the current statement with the current store. -/
abbrev Config := Stmt × Store

/-- Labels for the canonical small-step IMP LTS. -/
inductive StepLabel where
  | assign
  | seqStep (μ : StepLabel)
  | seqDone
  | ifTrue
  | ifFalse
  | whileTrue
  | whileFalse
  deriving DecidableEq, Repr

/-- Labeled small-step transition relation for IMP. -/
inductive Step : Config → StepLabel → Config → Prop where
  | assign {x : Var} {e : Expr} {σ : Store} :
      Step (.assign x e, σ) .assign (.skip, σ.update x (eval σ e))
  | seq_step {s1 s1' s2 : Stmt} {σ σ' : Store} {μ : StepLabel} :
      Step (s1, σ) μ (s1', σ') →
      Step (.seq s1 s2, σ) (.seqStep μ) (.seq s1' s2, σ')
  | seq_done {s2 : Stmt} {σ : Store} :
      Step (.seq .skip s2, σ) .seqDone (s2, σ)
  | if_true {cond : Expr} {s1 s2 : Stmt} {σ : Store} :
      eval σ cond ≠ 0 →
      Step (.ite cond s1 s2, σ) .ifTrue (s1, σ)
  | if_false {cond : Expr} {s1 s2 : Stmt} {σ : Store} :
      eval σ cond = 0 →
      Step (.ite cond s1 s2, σ) .ifFalse (s2, σ)
  | while_true {cond : Expr} {body : Stmt} {σ : Store} :
      eval σ cond ≠ 0 →
      Step (.while cond body, σ) .whileTrue (.seq body (.while cond body), σ)
  | while_false {cond : Expr} {body : Stmt} {σ : Store} :
      eval σ cond = 0 →
      Step (.while cond body, σ) .whileFalse (.skip, σ)

end Examples.IMP
