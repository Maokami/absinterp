import Cslib.Init

namespace Examples.IMP

/-- Program variables for the IMP language, represented as strings for extensibility. -/
abbrev Var := String

namespace Var
/-- Standard variable name used in examples. -/
def x0 : Var := "x0"
/-- Standard variable name used in examples. -/
def x1 : Var := "x1"
end Var

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
