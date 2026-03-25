import Cslib.Init

import Examples.IMP.Syntax

open Lean Macro

namespace Examples.IMP

declare_syntax_cat imp_expr
scoped syntax num : imp_expr
scoped syntax ident : imp_expr
scoped syntax "(" imp_expr ")" : imp_expr
scoped syntax:65 imp_expr:65 " + " imp_expr:66 : imp_expr

declare_syntax_cat imp_stmt
scoped syntax "skip" : imp_stmt
scoped syntax "(" imp_stmt ")" : imp_stmt
scoped syntax ident " := " imp_expr : imp_stmt
scoped syntax:60 imp_stmt:61 " ;; " imp_stmt:60 : imp_stmt
scoped syntax "if " imp_expr " then " imp_stmt " else " imp_stmt : imp_stmt

syntax "[imp_expr| " imp_expr "]" : term
syntax "[imp| " imp_stmt "]" : term

private def expandImpVar (x : TSyntax `ident) : MacroM (TSyntax `term) :=
  return Lean.quote (toString x.getId)

macro_rules
  | `([imp_expr| $n:num]) =>
      `(Expr.lit $n)
  | `([imp_expr| $x:ident]) => do
      let x' ← expandImpVar x
      `(Expr.var $x')
  | `([imp_expr| ($e:imp_expr)]) =>
      `([imp_expr| $e])
  | `([imp_expr| $e1:imp_expr + $e2:imp_expr]) =>
      `(Expr.add [imp_expr| $e1] [imp_expr| $e2])

macro_rules
  | `([imp| skip]) =>
      `(Stmt.skip)
  | `([imp| ($s:imp_stmt)]) =>
      `([imp| $s])
  | `([imp| $x:ident := $e:imp_expr]) => do
      let x' ← expandImpVar x
      `(Stmt.assign $x' [imp_expr| $e])
  | `([imp| $s1:imp_stmt ;; $s2:imp_stmt]) =>
      `(Stmt.seq [imp| $s1] [imp| $s2])
  | `([imp| if $cond:imp_expr then $s1:imp_stmt else $s2:imp_stmt]) =>
      `(Stmt.ite [imp_expr| $cond] [imp| $s1] [imp| $s2])

end Examples.IMP
