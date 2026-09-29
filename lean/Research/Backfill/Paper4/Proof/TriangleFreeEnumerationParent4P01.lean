import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent4P01
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 4 1).Connected ∧ (reps 4 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 4 1) (0 : Fin 4)
      (fun v => ([0, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_4_01_001 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({0} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 0, 1, 2] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_002 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({1} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 3, 1, 0, 2] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_004 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_005 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({0, 2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 2, 0, 4] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_008 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({3} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 4, 2, 3] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_010 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({1, 3} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 0, 2, 4] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_01_012 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) ({2, 3} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_4_01 : List (Finset (Fin 4)) := [{0}, {1}, {2}, {0, 2}, {3}, {1, 3}, {2, 3}]

theorem all_covers_4_01 : neighborhoods_4_01.Forall (fun S => ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 1) S ≃g reps 5 j)) := by
  exact And.intro cover_4_01_001 (And.intro cover_4_01_002 (And.intro cover_4_01_004 (And.intro cover_4_01_005 (And.intro cover_4_01_008 (And.intro cover_4_01_010 (cover_4_01_012))))))

theorem parent_layer (S : Finset (Fin 4))
    (hne : S.Nonempty) (hi : (reps 4 1).IsIndepSet (S : Set (Fin 4))) :
    ∃ j : Fin (repCount 5), Nonempty (augment (reps 4 1) S ≃g reps 5 j) := by
  have hcover : ∀ T : Finset (Fin 4), T.Nonempty →
      (reps 4 1).IsIndepSet (T : Set (Fin 4)) → T ∈ neighborhoods_4_01 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_4_01) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent4P01
