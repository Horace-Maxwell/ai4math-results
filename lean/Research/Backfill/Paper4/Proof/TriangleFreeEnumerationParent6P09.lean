import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P09
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 9).Connected ∧ (reps 6 9).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 9) (0 : Fin 6)
      (fun v => ([0, 2, 2, 3, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_09_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨21, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 0, 1, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 6, 5, 2, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 2, 5, 6, 1, 0, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 6, 1, 5, 2, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 2, 6, 1, 0, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨37, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 4, 0, 2, 6, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_007 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({0, 1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 4, 3, 1, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨19, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 5, 3, 0, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 4, 2, 5, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 0, 1, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨33, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 1, 3, 4, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨23, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 0, 1, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 3, 6, 2, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 5, 6, 2, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_038 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({1, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨50, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 2, 1, 3, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨40, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 6, 1, 5, 3, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨38, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 5, 0, 6, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_09_056 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) ({3, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 4, 0, 5, 3, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_09 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {4}, {3, 4}, {5}, {1, 5}, {2, 5}, {1, 2, 5}, {3, 5}, {4, 5}, {3, 4, 5}]

theorem all_covers_6_09 : neighborhoods_6_09.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 9) S ≃g reps 7 j)) := by
  exact And.intro cover_6_09_001 (And.intro cover_6_09_002 (And.intro cover_6_09_003 (And.intro cover_6_09_004 (And.intro cover_6_09_005 (And.intro cover_6_09_006 (And.intro cover_6_09_007 (And.intro cover_6_09_008 (And.intro cover_6_09_009 (And.intro cover_6_09_016 (And.intro cover_6_09_024 (And.intro cover_6_09_032 (And.intro cover_6_09_034 (And.intro cover_6_09_036 (And.intro cover_6_09_038 (And.intro cover_6_09_040 (And.intro cover_6_09_048 (cover_6_09_056)))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 9).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 9) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 9).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_09 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_09) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P09
