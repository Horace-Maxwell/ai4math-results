import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P10
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 10).Connected ∧ (reps 6 10).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 10) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_10_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 2, 1, 0, 4, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 5, 6, 3, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 5, 4, 0, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 5, 6, 3, 0, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨20, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 0, 5, 6, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 3, 2, 1, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 5, 4, 3, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨20, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 3, 6, 5, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 2, 3, 4, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 5, 1, 2, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨24, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 5, 6, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 2, 1, 0, 4, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 5, 4, 0, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_037 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨50, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 4, 5, 6, 1, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨41, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 6, 3, 2, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_041 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({0, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 5, 4, 6, 2, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨41, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 1, 2, 3, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_10_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨49, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 0, 6, 4, 2, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_10 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {1, 4}, {2, 4}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {3, 5}, {0, 3, 5}, {4, 5}, {2, 4, 5}]

theorem all_covers_6_10 : neighborhoods_6_10.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 10) S ≃g reps 7 j)) := by
  exact And.intro cover_6_10_001 (And.intro cover_6_10_002 (And.intro cover_6_10_004 (And.intro cover_6_10_005 (And.intro cover_6_10_008 (And.intro cover_6_10_009 (And.intro cover_6_10_010 (And.intro cover_6_10_016 (And.intro cover_6_10_018 (And.intro cover_6_10_020 (And.intro cover_6_10_032 (And.intro cover_6_10_033 (And.intro cover_6_10_036 (And.intro cover_6_10_037 (And.intro cover_6_10_040 (And.intro cover_6_10_041 (And.intro cover_6_10_048 (cover_6_10_052)))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 10).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 10) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 10).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_10 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_10) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P10
