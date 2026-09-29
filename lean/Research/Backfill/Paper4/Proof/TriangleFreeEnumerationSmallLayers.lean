import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationSmallLayers
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem rep_valid_1_00 : (reps 1 0).Connected ∧ (reps 1 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 1 0) (0 : Fin 1)
      (fun v => ([0] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_2_00 : (reps 2 0).Connected ∧ (reps 2 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 2 0) (0 : Fin 2)
      (fun v => ([0, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_3_00 : (reps 3 0).Connected ∧ (reps 3 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 3 0) (0 : Fin 3)
      (fun v => ([0, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem small_representatives_valid (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3) :
    ∀ i : Fin (repCount n), (reps n i).Connected ∧ (reps n i).CliqueFree 3 := by
  interval_cases n <;> intro i <;> fin_cases i
  · exact rep_valid_1_00
  · exact rep_valid_2_00
  · exact rep_valid_3_00

theorem cover_1_00_001 : ∃ j : Fin (repCount 2),
    Nonempty (augment (reps 1 0) ({0} : Finset (Fin 1)) ≃g reps 2 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1] : Fin 2 → Fin 2) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_1_00 : List (Finset (Fin 1)) := [{0}]

theorem all_covers_1_00 : neighborhoods_1_00.Forall (fun S => ∃ j : Fin (repCount 2),
    Nonempty (augment (reps 1 0) S ≃g reps 2 j)) := by
  exact cover_1_00_001

theorem parent_layer_1_00 (S : Finset (Fin 1))
    (hne : S.Nonempty) (hi : (reps 1 0).IsIndepSet (S : Set (Fin 1))) :
    ∃ j : Fin (repCount 2), Nonempty (augment (reps 1 0) S ≃g reps 2 j) := by
  have hcover : ∀ T : Finset (Fin 1), T.Nonempty →
      (reps 1 0).IsIndepSet (T : Set (Fin 1)) → T ∈ neighborhoods_1_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_1_00) S (hcover S hne hi)

theorem layer_1 : LayerStep (reps 1) (reps 2) := by
  intro i S hne hi
  fin_cases i
  exact parent_layer_1_00 S hne hi

theorem cover_2_00_001 : ∃ j : Fin (repCount 3),
    Nonempty (augment (reps 2 0) ({0} : Finset (Fin 2)) ≃g reps 3 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2] : Fin 3 → Fin 3) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_2_00_002 : ∃ j : Fin (repCount 3),
    Nonempty (augment (reps 2 0) ({1} : Finset (Fin 2)) ≃g reps 3 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 2] : Fin 3 → Fin 3) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_2_00 : List (Finset (Fin 2)) := [{0}, {1}]

theorem all_covers_2_00 : neighborhoods_2_00.Forall (fun S => ∃ j : Fin (repCount 3),
    Nonempty (augment (reps 2 0) S ≃g reps 3 j)) := by
  exact And.intro cover_2_00_001 (cover_2_00_002)

theorem parent_layer_2_00 (S : Finset (Fin 2))
    (hne : S.Nonempty) (hi : (reps 2 0).IsIndepSet (S : Set (Fin 2))) :
    ∃ j : Fin (repCount 3), Nonempty (augment (reps 2 0) S ≃g reps 3 j) := by
  have hcover : ∀ T : Finset (Fin 2), T.Nonempty →
      (reps 2 0).IsIndepSet (T : Set (Fin 2)) → T ∈ neighborhoods_2_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_2_00) S (hcover S hne hi)

theorem layer_2 : LayerStep (reps 2) (reps 3) := by
  intro i S hne hi
  fin_cases i
  exact parent_layer_2_00 S hne hi

#print axioms small_representatives_valid
#print axioms layer_1
#print axioms layer_2

end CodexPaper4.TriangleFreeEnumerationSmallLayers
