import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P14
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 14).Connected ∧ (reps 6 14).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 14) (0 : Fin 6)
      (fun v => ([0, 1, 2, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_14_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 3, 2, 6, 5, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 3, 2, 6, 5, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 1, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 0, 2, 3, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 1, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 1, 5, 6, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 6, 5, 1, 4, 3, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 6, 3, 2, 0, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 2, 1, 4, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨51, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 6, 4, 5, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_021 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({0, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 0, 2, 1, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 6, 2, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨51, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 4, 1, 2, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 6, 5, 1, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_14_042 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) ({1, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 5, 4, 6, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_14 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {1, 3}, {4}, {0, 4}, {1, 4}, {2, 4}, {0, 2, 4}, {5}, {1, 5}, {2, 5}, {3, 5}, {1, 3, 5}]

theorem all_covers_6_14 : neighborhoods_6_14.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 14) S ≃g reps 7 j)) := by
  exact And.intro cover_6_14_001 (And.intro cover_6_14_002 (And.intro cover_6_14_004 (And.intro cover_6_14_005 (And.intro cover_6_14_008 (And.intro cover_6_14_010 (And.intro cover_6_14_016 (And.intro cover_6_14_017 (And.intro cover_6_14_018 (And.intro cover_6_14_020 (And.intro cover_6_14_021 (And.intro cover_6_14_032 (And.intro cover_6_14_034 (And.intro cover_6_14_036 (And.intro cover_6_14_040 (cover_6_14_042)))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 14).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 14) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 14).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_14 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_14) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P14
