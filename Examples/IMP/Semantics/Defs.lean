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

/-- A configuration is either a running statement with a store, or a terminated store. -/
inductive Config where
  | running (s : Stmt) (σ : Store)
  | done (σ : Store)

/-- Small-step transition relation for IMP. -/
inductive Step : Config → Config → Prop where
  | skip {σ : Store} :
      Step (.running .skip σ) (.done σ)
  | assign {x : Var} {e : Expr} {σ : Store} :
      Step (.running (.assign x e) σ) (.done (σ.update x (eval σ e)))
  | seq_step {s1 s1' s2 : Stmt} {σ σ' : Store} :
      Step (.running s1 σ) (.running s1' σ') →
      Step (.running (.seq s1 s2) σ) (.running (.seq s1' s2) σ')
  | seq_done {s1 s2 : Stmt} {σ σ' : Store} :
      Step (.running s1 σ) (.done σ') →
      Step (.running (.seq s1 s2) σ) (.running s2 σ')
  | if_true {cond : Expr} {s1 s2 : Stmt} {σ : Store} :
      eval σ cond ≠ 0 →
      Step (.running (.ite cond s1 s2) σ) (.running s1 σ)
  | if_false {cond : Expr} {s1 s2 : Stmt} {σ : Store} :
      eval σ cond = 0 →
      Step (.running (.ite cond s1 s2) σ) (.running s2 σ)

end Examples.IMP
