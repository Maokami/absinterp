import Cslib.Init

import AbsInterpLTS.Framework.Soundness
import Examples.IMP.Abstraction.Defs

namespace Examples.IMP

open AbsInterpLTS.Framework

/--
`ActiveIn program s` means that `s` can arise as a control location while
executing the loop-free textbook IMP program `program`.

For `seq`, the left phase keeps the right suffix attached; once the left side
finishes, execution continues inside the right subprogram directly.
-/
inductive ActiveIn : Stmt → Stmt → Prop where
  | skip :
      ActiveIn .skip .skip
  | assign {x : Var} {e : Expr} :
      ActiveIn (.assign x e) (.assign x e)
  | assignDone {x : Var} {e : Expr} :
      ActiveIn (.assign x e) .skip
  | seqLeft {s1 s2 t : Stmt} :
      ActiveIn s1 t →
      ActiveIn (.seq s1 s2) (.seq t s2)
  | seqRight {s1 s2 t : Stmt} :
      ActiveIn s2 t →
      ActiveIn (.seq s1 s2) t
  | iteRoot {cond : Expr} {s1 s2 : Stmt} :
      ActiveIn (.ite cond s1 s2) (.ite cond s1 s2)
  | iteThen {cond : Expr} {s1 s2 t : Stmt} :
      ActiveIn s1 t →
      ActiveIn (.ite cond s1 s2) t
  | iteElse {cond : Expr} {s1 s2 t : Stmt} :
      ActiveIn s2 t →
      ActiveIn (.ite cond s1 s2) t

/-- Every IMP program is active at its own initial control location. -/
theorem ActiveIn.self (program : Stmt) :
    ActiveIn program program := by
  induction program with
  | skip =>
      exact ActiveIn.skip
  | assign =>
      exact ActiveIn.assign
  | seq _ _ ih1 _ =>
      exact ActiveIn.seqLeft ih1
  | ite =>
      exact ActiveIn.iteRoot

/-- Restrict abstract configurations to control states active in a fixed program. -/
def gammaProgramConfigOf
    {Abstract : Type _}
    (program : Stmt)
    (gamma : Abstract → Set Int) :
    Gamma (ConfigSharp Abstract) Config :=
  fun κ => { c : Config |
    ActiveIn program (controlOfConfig c) ∧
      c ∈ gammaConfigOf gamma κ }

@[simp] theorem mem_gammaProgramConfigOf_mk
    {Abstract : Type _}
    {program : Stmt}
    {gamma : Abstract → Set Int}
    {κ : ConfigSharp Abstract}
    {s : Stmt}
    {σ : Store} :
    (s, σ) ∈ gammaProgramConfigOf program gamma κ ↔
      ActiveIn program s ∧
      σ ∈ gammaStoreOf gamma (κ s) := by
  rfl

end Examples.IMP
