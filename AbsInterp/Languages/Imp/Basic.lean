/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import Mathlib.Data.Int.Basic

@[expose] public section

/-!
# IMP (small-step)

A minimal IMP-like language used as a first instance for abstract interpretation.
This file defines syntax, state, and a small-step transition relation.
-/

namespace AbsInterp

namespace Imp

universe u

variable {Var : Type u} [DecidableEq Var]

/-- Program state as a total map from variables to integers. -/
abbrev State (Var : Type u) := Var -> Int

/-- Update a state at a variable. -/
def State.update (sigma : State Var) (x : Var) (v : Int) : State Var :=
  fun y => if y = x then v else sigma y

/-- Arithmetic expressions. -/
inductive AExp (Var : Type u)
  | lit : Int -> AExp Var
  | var : Var -> AExp Var
  | add : AExp Var -> AExp Var -> AExp Var
  | sub : AExp Var -> AExp Var -> AExp Var
  | mul : AExp Var -> AExp Var -> AExp Var
  deriving DecidableEq

/-- Boolean expressions. -/
inductive BExp (Var : Type u)
  | tt : BExp Var
  | ff : BExp Var
  | eq : AExp Var -> AExp Var -> BExp Var
  | le : AExp Var -> AExp Var -> BExp Var
  | not : BExp Var -> BExp Var
  | and : BExp Var -> BExp Var -> BExp Var
  deriving DecidableEq

/-- Statements. -/
inductive Stmt (Var : Type u)
  | skip : Stmt Var
  | assign : Var -> AExp Var -> Stmt Var
  | seq : Stmt Var -> Stmt Var -> Stmt Var
  | ite : BExp Var -> Stmt Var -> Stmt Var -> Stmt Var
  | while : BExp Var -> Stmt Var -> Stmt Var
  deriving DecidableEq

/-- Expression evaluation. -/
def AExp.eval : AExp Var -> State Var -> Int
  | .lit n, _ => n
  | .var x, sigma => sigma x
  | .add a b, sigma => AExp.eval a sigma + AExp.eval b sigma
  | .sub a b, sigma => AExp.eval a sigma - AExp.eval b sigma
  | .mul a b, sigma => AExp.eval a sigma * AExp.eval b sigma

/-- Boolean evaluation. -/
def BExp.eval : BExp Var -> State Var -> Bool
  | .tt, _ => true
  | .ff, _ => false
  | .eq a b, sigma => decide (AExp.eval a sigma = AExp.eval b sigma)
  | .le a b, sigma => decide (AExp.eval a sigma <= AExp.eval b sigma)
  | .not b, sigma => !BExp.eval b sigma
  | .and a b, sigma => BExp.eval a sigma && BExp.eval b sigma

/-- Configurations for small-step semantics. -/
abbrev Config (Var : Type u) := Stmt Var × State Var

/-- Small-step transition relation. -/
inductive Step : Config Var -> Config Var -> Prop
  | assign (x : Var) (a : AExp Var) (sigma : State Var) :
      Step (Stmt.assign x a, sigma)
        (Stmt.skip, State.update sigma x (AExp.eval a sigma))
  | seq_step (s1 s1' s2 : Stmt Var) (sigma sigma' : State Var) :
      Step (s1, sigma) (s1', sigma') ->
      Step (Stmt.seq s1 s2, sigma) (Stmt.seq s1' s2, sigma')
  | seq_skip (s2 : Stmt Var) (sigma : State Var) :
      Step (Stmt.seq Stmt.skip s2, sigma) (s2, sigma)
  | ite_true (b : BExp Var) (s1 s2 : Stmt Var) (sigma : State Var) :
      BExp.eval b sigma = true ->
      Step (Stmt.ite b s1 s2, sigma) (s1, sigma)
  | ite_false (b : BExp Var) (s1 s2 : Stmt Var) (sigma : State Var) :
      BExp.eval b sigma = false ->
      Step (Stmt.ite b s1 s2, sigma) (s2, sigma)
  | while_step (b : BExp Var) (s : Stmt Var) (sigma : State Var) :
      Step (Stmt.while b s, sigma)
        (Stmt.ite b (Stmt.seq s (Stmt.while b s)) Stmt.skip, sigma)

end Imp

end AbsInterp
