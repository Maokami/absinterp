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

@[simp] theorem step_skip_iff {σ : Store} {μ : StepLabel} {c' : Config} :
    Step (.running .skip σ) μ c' ↔ μ = .skip ∧ c' = .done σ := by
  constructor
  · intro hStep
    cases hStep
    simp
  · rintro ⟨rfl, rfl⟩
    exact Step.skip

@[simp] theorem step_assign_iff
    {x : Var} {e : Expr} {σ : Store} {μ : StepLabel} {c' : Config} :
    Step (.running (.assign x e) σ) μ c' ↔
      μ = .assign ∧ c' = .done (σ.update x (eval σ e)) := by
  constructor
  · intro hStep
    cases hStep
    simp
  · rintro ⟨rfl, rfl⟩
    exact Step.assign

@[simp] theorem step_ifTrue_iff
    {cond : Expr} {s1 s2 : Stmt} {σ : Store} {c' : Config} :
    Step (.running (.ite cond s1 s2) σ) .ifTrue c' ↔
      eval σ cond ≠ 0 ∧ c' = .running s1 σ := by
  constructor
  · intro hStep
    cases hStep with
    | if_true hCond =>
        simp [hCond]
  · rintro ⟨hCond, rfl⟩
    exact Step.if_true hCond

@[simp] theorem step_ifFalse_iff
    {cond : Expr} {s1 s2 : Stmt} {σ : Store} {c' : Config} :
    Step (.running (.ite cond s1 s2) σ) .ifFalse c' ↔
      eval σ cond = 0 ∧ c' = .running s2 σ := by
  constructor
  · intro hStep
    cases hStep with
    | if_false hCond =>
        simp [hCond]
  · rintro ⟨hCond, rfl⟩
    exact Step.if_false hCond

theorem Step.seqStep_inv
    {s1 s2 : Stmt} {σ : Store} {μ : StepLabel} {c' : Config}
    (hStep : Step (.running (.seq s1 s2) σ) (.seqStep μ) c') :
    ∃ s1' σ',
      c' = .running (.seq s1' s2) σ' ∧
      Step (.running s1 σ) μ (.running s1' σ') := by
  cases hStep with
  | seq_step hInner =>
      exact ⟨_, _, rfl, hInner⟩

theorem Step.seqDone_inv
    {s1 s2 : Stmt} {σ : Store} {μ : StepLabel} {c' : Config}
    (hStep : Step (.running (.seq s1 s2) σ) (.seqDone μ) c') :
    ∃ σ',
      c' = .running s2 σ' ∧
      Step (.running s1 σ) μ (.done σ') := by
  cases hStep with
  | seq_done hInner =>
      exact ⟨_, rfl, hInner⟩

end Examples.IMP
