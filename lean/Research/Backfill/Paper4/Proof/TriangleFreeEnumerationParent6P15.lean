import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P15
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 15).Connected ∧ (reps 6 15).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 15) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_15_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 3, 4, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 3, 2, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 0, 5, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨48, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 4, 3, 2, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 3, 2, 1, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨46, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 6, 5, 0, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨48, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 1, 0, 2, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 6, 5, 4, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 5, 4, 1, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 3, 0, 1, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 6, 5, 1, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 5, 4, 6, 1, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 3, 0, 6, 1, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨50, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 6, 5, 4, 0, 2, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨56, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 6, 3, 2, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_15_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨56, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 3, 2, 1, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_15 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {1, 4}, {2, 4}, {5}, {1, 5}, {2, 5}, {4, 5}, {1, 4, 5}, {2, 4, 5}]

theorem all_covers_6_15 : neighborhoods_6_15.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 15) S ≃g reps 7 j)) := by
  exact And.intro cover_6_15_001 (And.intro cover_6_15_002 (And.intro cover_6_15_004 (And.intro cover_6_15_005 (And.intro cover_6_15_008 (And.intro cover_6_15_009 (And.intro cover_6_15_010 (And.intro cover_6_15_016 (And.intro cover_6_15_018 (And.intro cover_6_15_020 (And.intro cover_6_15_032 (And.intro cover_6_15_034 (And.intro cover_6_15_036 (And.intro cover_6_15_048 (And.intro cover_6_15_050 (cover_6_15_052)))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 15).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 15) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 15).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_15 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_15) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P15
