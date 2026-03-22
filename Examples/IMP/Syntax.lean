import Cslib.Init

namespace Examples.IMP

/-- Program variables for the IMP language. Two variables suffice for examples. -/
inductive Var where
  | x0
  | x1
  deriving DecidableEq, Repr

/-- Arithmetic expressions: integer literals, variable reads, and addition. -/
inductive Expr where
  | lit (n : Int)
  | var (x : Var)
  | add (e1 e2 : Expr)
  deriving DecidableEq, Repr

/-- Statements: the core IMP constructs (no loops in this subset). -/
inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (s1 s2 : Stmt)
  | ite (cond : Expr) (s1 s2 : Stmt)
  deriving DecidableEq, Repr

end Examples.IMP
