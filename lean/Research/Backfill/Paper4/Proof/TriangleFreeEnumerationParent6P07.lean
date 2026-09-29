import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P07
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 7).Connected ∧ (reps 6 7).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 7) (0 : Fin 6)
      (fun v => ([0, 2, 1, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_07_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 6, 2, 0, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 0, 1, 6, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 3, 0, 2, 5, 6, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 2, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 6, 3, 5, 1, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 3, 4, 6, 5, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 1, 3, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 1, 4, 3, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 2, 4, 5, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 3, 1, 6, 0, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_028 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 1, 5, 3, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 6, 5, 2, 0, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 2, 0, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 2, 3, 1, 0, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_035 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({0, 1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 0, 2, 6, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 1, 2, 5, 0, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 6, 3, 5, 1, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 6, 1, 5, 2, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_07_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 1, 3, 6, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_07 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {3}, {2, 3}, {4}, {1, 4}, {2, 4}, {3, 4}, {2, 3, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {2, 5}, {4, 5}, {1, 4, 5}, {2, 4, 5}]

theorem all_covers_6_07 : neighborhoods_6_07.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 7) S ≃g reps 7 j)) := by
  exact And.intro cover_6_07_001 (And.intro cover_6_07_002 (And.intro cover_6_07_003 (And.intro cover_6_07_004 (And.intro cover_6_07_008 (And.intro cover_6_07_012 (And.intro cover_6_07_016 (And.intro cover_6_07_018 (And.intro cover_6_07_020 (And.intro cover_6_07_024 (And.intro cover_6_07_028 (And.intro cover_6_07_032 (And.intro cover_6_07_033 (And.intro cover_6_07_034 (And.intro cover_6_07_035 (And.intro cover_6_07_036 (And.intro cover_6_07_048 (And.intro cover_6_07_050 (cover_6_07_052))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 7).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 7) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 7).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_07 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_07) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P07
