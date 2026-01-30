/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Cslib.Init
public import AbsInterp.Languages.Imp.Basic
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# IMP collecting semantics

This file defines the standard collecting semantics for IMP statements
via the reflexive-transitive closure of the small-step relation.
-/

namespace AbsInterp

namespace Imp

universe u

variable {Var : Type u} [DecidableEq Var]

/-- Reflexive-transitive closure of the small-step relation. -/
abbrev StepStar : Config Var -> Config Var -> Prop :=
  Relation.ReflTransGen (Step (Var := Var))

/-- Termination: a statement reaches `skip` in zero or more steps. -/
def Terminates (s : Stmt Var) (σ σ' : State Var) : Prop :=
  StepStar (s, σ) (Stmt.skip, σ')

/-- Collecting semantics as a post transformer over sets of states. -/
def Post (s : Stmt Var) : Set (State Var) -> Set (State Var) :=
  fun S => {σ' | ∃ σ, σ ∈ S ∧ Terminates s σ σ'}

/-- Collecting semantics over configurations (all reachable configurations). -/
def ReachConfigs (s : Stmt Var) : Set (State Var) -> Set (Config Var) :=
  fun S => {cfg | ∃ σ, σ ∈ S ∧ StepStar (s, σ) cfg}

/-- Collecting semantics over states (all reachable states). -/
def ReachStates (s : Stmt Var) : Set (State Var) -> Set (State Var) :=
  fun S => {σ' | ∃ s', (s', σ') ∈ ReachConfigs s S}

section Lemmas

/-- Terminating states are reachable states. -/
theorem post_subset_reachStates (s : Stmt Var) (S : Set (State Var)) :
    Post s S ⊆ ReachStates s S := by
  intro σ' h
  rcases h with ⟨σ, hσ, hterm⟩
  refine ⟨Stmt.skip, ?_⟩
  exact ⟨σ, hσ, hterm⟩

/-- Initial states are reachable configurations (reflexivity). -/
theorem initial_reachConfigs (s : Stmt Var) (S : Set (State Var)) :
    S ⊆ {σ | (s, σ) ∈ ReachConfigs s S} := by
  intro σ hσ
  show (s, σ) ∈ ReachConfigs s S
  refine ⟨σ, hσ, ?_⟩
  exact Relation.ReflTransGen.refl

/-- Reachable states are monotone in the initial set of states. -/
theorem reachStates_mono (s : Stmt Var) {S T : Set (State Var)} (h : S ⊆ T) :
    ReachStates s S ⊆ ReachStates s T := by
  intro σ' hσ'
  rcases hσ' with ⟨s', hs'⟩
  rcases hs' with ⟨σ, hσS, hstep⟩
  have hσT : σ ∈ T := h hσS
  refine ⟨s', ?_⟩
  exact ⟨σ, hσT, hstep⟩

end Lemmas

end Imp

end AbsInterp
