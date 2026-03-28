import Cslib.Init
import Mathlib.Data.Set.Lattice

import AbsInterp.Framework.Semantics
import AbsInterp.Framework.Iteration.Collecting
import AbsInterp.Instances.LTS.Semantics.Collecting
import AbsInterp.Instances.LTS.Semantics.Lemmas

/-!
# Collecting–Trace Bridge

This file connects the two concrete semantic paths of the framework:

1. **Trace path** (labeled): `postStep lts label` → `liftTracePost` → traces
2. **Collecting path** (unlabeled): `postAny lts` → `CollectingStep` → `kleeneNat`

The headline result is that the Kleene chain `kleeneNat (n+1)` equals the union
of `liftTracePost` over all traces of length `≤ n`.
-/

namespace AbsInterp
namespace Instances
namespace LTS

open Cslib
open AbsInterp.Framework

universe u v

variable
    {State : Type u}
    {Label : Type v}
    (lts : Cslib.LTS State Label)

/--
A single labeled step from a Kleene iterate lands in the next iterate.
-/
theorem postStep_kleeneNat_subset
    (label : Label)
    (init : Set State)
    (m : Nat) :
    postStep lts label ((postAny_collectingStep lts).kleeneNat init m) ⊆
      (postAny_collectingStep lts).kleeneNat init (m + 1) := by
  intro s' hs'
  simp [CollectingStep.kleeneNat_succ]
  right
  exact postStep_subset_postAny lts label _ hs'

/--
A lifted trace from Kleene iterate `m` lands in iterate `m + labels.length`.
-/
theorem liftTracePost_kleeneNat_subset
    (labels : List Label)
    (init : Set State)
    (m : Nat) :
    liftTracePost (postStep lts) labels ((postAny_collectingStep lts).kleeneNat init m) ⊆
      (postAny_collectingStep lts).kleeneNat init (m + labels.length) := by
  induction labels generalizing m with
  | nil =>
      simp
  | cons label labels ih =>
      simp only [liftTracePost_cons, composePost, List.length_cons]
      have hSub := postStep_kleeneNat_subset lts label init m
      have hMono := liftTracePost_monotone_of_pointwise
        (hStepMono := fun l => postStep_monotone lts l) labels hSub
      have hlen : m + (labels.length + 1) = (m + 1) + labels.length := by omega
      rw [hlen]
      exact Set.Subset.trans hMono (ih (m + 1))

/--
**Theorem 1**: Any labeled trace of length `≤ n` from `init` is captured by
`kleeneNat (n + 1)`.
-/
theorem liftTracePost_subset_kleeneNat
    (labels : List Label)
    (init : Set State)
    (n : Nat)
    (hLen : labels.length ≤ n) :
    liftTracePost (postStep lts) labels init ⊆
      (postAny_collectingStep lts).kleeneNat init (n + 1) :=
  calc
    liftTracePost (postStep lts) labels init
    _ ⊆ liftTracePost (postStep lts) labels
          ((postAny_collectingStep lts).kleeneNat init 1) :=
        liftTracePost_monotone_of_pointwise
          (hStepMono := fun label => postStep_monotone lts label)
          labels
          ((postAny_collectingStep lts).init_subset_kleeneNat_succ 0 init)
    _ ⊆ (postAny_collectingStep lts).kleeneNat init (1 + labels.length) :=
        liftTracePost_kleeneNat_subset lts labels init 1
    _ ⊆ (postAny_collectingStep lts).kleeneNat init (n + 1) :=
        (postAny_collectingStep lts).kleeneNat_chain_of_le (by omega) init

/--
**Theorem 2**: Every state in `kleeneNat (n + 1)` has a witnessing labeled trace
of length `≤ n`.
-/
theorem kleeneNat_subset_iUnion_liftTracePost
    (init : Set State)
    (n : Nat)
    (s : State)
    (hs : s ∈ (postAny_collectingStep lts).kleeneNat init (n + 1)) :
    ∃ labels : List Label, labels.length ≤ n ∧
      s ∈ liftTracePost (postStep lts) labels init := by
  induction n generalizing s with
  | zero =>
      simp [CollectingStep.kleeneNat_succ, CollectingStep.kleeneNat_zero] at hs
      rcases hs with hInit | hPost
      · exact ⟨[], by simp, hInit⟩
      · change s ∈ postAny lts ∅ at hPost
        simp [mem_postAny] at hPost
  | succ n ih =>
      simp only [CollectingStep.kleeneNat_succ] at hs
      rcases hs with hInit | hPost
      · exact ⟨[], by simp, hInit⟩
      · change s ∈ postAny lts ((postAny_collectingStep lts).kleeneNat init (n + 1)) at hPost
        rw [mem_postAny] at hPost
        rcases hPost with ⟨s', hs'mem, label, htr⟩
        rcases ih s' hs'mem with ⟨labels, hlen, hTrace⟩
        refine ⟨labels ++ [label], ?_, ?_⟩
        · simp; omega
        · rw [liftTracePost_snoc_apply]
          exact (Cslib.LTS.mem_setImage
            (lts := lts)
            (S := liftTracePost (postStep lts) labels init)
            (μ := label)
            (s' := s)).2 ⟨s', hTrace, htr⟩

/--
**Theorem 3**: Exact characterization of the Kleene chain in terms of trace unions.
-/
theorem kleeneNat_eq_iUnion_liftTracePost
    (init : Set State)
    (n : Nat) :
    (postAny_collectingStep lts).kleeneNat init (n + 1) =
      ⋃ (labels : List Label) (_ : labels.length ≤ n),
        liftTracePost (postStep lts) labels init := by
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · intro hs
    rcases kleeneNat_subset_iUnion_liftTracePost lts init n s hs with ⟨labels, hlen, hmem⟩
    exact ⟨labels, hlen, hmem⟩
  · intro ⟨labels, hlen, hmem⟩
    exact liftTracePost_subset_kleeneNat lts labels init n hlen hmem

end LTS
end Instances
end AbsInterp
