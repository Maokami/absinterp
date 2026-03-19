import Cslib.Init

import Examples.IMP.Semantics.Defs

namespace Examples.IMP

@[simp] theorem Store.update_same (σ : Store) (x : Var) (v : Int) :
    (σ.update x v) x = v := by
  simp [Store.update]

@[simp] theorem Store.update_other (σ : Store) (x y : Var) (v : Int) (hne : x ≠ y) :
    (σ.update x v) y = σ y := by
  simp [Store.update, hne]

@[simp] theorem eval_lit (σ : Store) (n : Int) :
    eval σ (.lit n) = n := rfl

@[simp] theorem eval_var (σ : Store) (x : Var) :
    eval σ (.var x) = σ x := rfl

@[simp] theorem eval_add (σ : Store) (e1 e2 : Expr) :
    eval σ (.add e1 e2) = eval σ e1 + eval σ e2 := rfl

end Examples.IMP
