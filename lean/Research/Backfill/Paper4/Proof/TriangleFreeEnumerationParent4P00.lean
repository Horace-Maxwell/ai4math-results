import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent4P00
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 4 0).Connected ∧ (reps 4 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 4 0) (0 : Fin 4)
      (fun v => ([0, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_4_00_001 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({0} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 1, 2, 3, 0] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_002 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({1} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 2, 3, 0] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_003 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({0, 1} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 0, 1, 2] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_004 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 4, 3, 0] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_005 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({0, 2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 4, 1, 2] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_006 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({1, 2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 4, 1, 2] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_007 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({0, 1, 2} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 0, 1] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_4_00_008 : ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) ({3} : Finset (Fin 4)) ≃g reps 5 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 4, 3] : Fin 5 → Fin 5) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_4_00 : List (Finset (Fin 4)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}]

theorem all_covers_4_00 : neighborhoods_4_00.Forall (fun S => ∃ j : Fin (repCount 5),
    Nonempty (augment (reps 4 0) S ≃g reps 5 j)) := by
  exact And.intro cover_4_00_001 (And.intro cover_4_00_002 (And.intro cover_4_00_003 (And.intro cover_4_00_004 (And.intro cover_4_00_005 (And.intro cover_4_00_006 (And.intro cover_4_00_007 (cover_4_00_008)))))))

theorem parent_layer (S : Finset (Fin 4))
    (hne : S.Nonempty) (hi : (reps 4 0).IsIndepSet (S : Set (Fin 4))) :
    ∃ j : Fin (repCount 5), Nonempty (augment (reps 4 0) S ≃g reps 5 j) := by
  have hcover : ∀ T : Finset (Fin 4), T.Nonempty →
      (reps 4 0).IsIndepSet (T : Set (Fin 4)) → T ∈ neighborhoods_4_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_4_00) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent4P00
