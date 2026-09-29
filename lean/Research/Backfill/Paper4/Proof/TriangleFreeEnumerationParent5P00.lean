import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent5P00
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 5 0).Connected ∧ (reps 5 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 0) (0 : Fin 5)
      (fun v => ([0, 2, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_5_00_001 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 4, 5, 1, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_002 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 4, 5, 1, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_003 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 5, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_004 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 2, 5, 1, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_005 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 3, 5, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_006 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({1, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 2, 3, 5, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_007 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 1, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 5, 0, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_008 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 5, 2, 1, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_009 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 5, 3, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_010 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({1, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 2, 5, 3, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_011 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 1, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 0, 5, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_012 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({2, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 2, 3, 0, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_013 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 2, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 5, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_014 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({1, 2, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 5, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_015 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({0, 1, 2, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_00_016 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) ({4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 5, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_5_00 : List (Finset (Fin 5)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {4}]

theorem all_covers_5_00 : neighborhoods_5_00.Forall (fun S => ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 0) S ≃g reps 6 j)) := by
  exact And.intro cover_5_00_001 (And.intro cover_5_00_002 (And.intro cover_5_00_003 (And.intro cover_5_00_004 (And.intro cover_5_00_005 (And.intro cover_5_00_006 (And.intro cover_5_00_007 (And.intro cover_5_00_008 (And.intro cover_5_00_009 (And.intro cover_5_00_010 (And.intro cover_5_00_011 (And.intro cover_5_00_012 (And.intro cover_5_00_013 (And.intro cover_5_00_014 (And.intro cover_5_00_015 (cover_5_00_016)))))))))))))))

theorem parent_layer (S : Finset (Fin 5))
    (hne : S.Nonempty) (hi : (reps 5 0).IsIndepSet (S : Set (Fin 5))) :
    ∃ j : Fin (repCount 6), Nonempty (augment (reps 5 0) S ≃g reps 6 j) := by
  have hcover : ∀ T : Finset (Fin 5), T.Nonempty →
      (reps 5 0).IsIndepSet (T : Set (Fin 5)) → T ∈ neighborhoods_5_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_5_00) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent5P00
