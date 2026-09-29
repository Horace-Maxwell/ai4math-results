import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P01
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 1).Connected ∧ (reps 6 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 1) (0 : Fin 6)
      (fun v => ([0, 1, 2, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_01_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 4, 5, 0, 2, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 1, 0, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 5, 3, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 2, 1, 0, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 5, 3, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 5, 6, 1, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 0, 5, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 6, 4, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 2, 5, 4, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 2, 1, 6, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_021 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 2, 6, 1, 5, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 2, 3, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_025 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 2, 3, 6, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 6, 2, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 2, 5, 6, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 2, 1, 4, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_037 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 2, 6, 5, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_041 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 2, 3, 0, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 2, 5, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_049 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨33, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 5, 6, 1, 2, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 4, 2, 6, 0, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_053 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 1, 6, 2, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_056 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({3, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 5, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_01_057 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) ({0, 3, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨46, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 3, 6, 1, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_01 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {0, 4}, {2, 4}, {0, 2, 4}, {3, 4}, {0, 3, 4}, {5}, {0, 5}, {2, 5}, {0, 2, 5}, {3, 5}, {0, 3, 5}, {4, 5}, {0, 4, 5}, {2, 4, 5}, {0, 2, 4, 5}, {3, 4, 5}, {0, 3, 4, 5}]

theorem all_covers_6_01 : neighborhoods_6_01.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 1) S ≃g reps 7 j)) := by
  exact And.intro cover_6_01_001 (And.intro cover_6_01_002 (And.intro cover_6_01_004 (And.intro cover_6_01_005 (And.intro cover_6_01_008 (And.intro cover_6_01_009 (And.intro cover_6_01_010 (And.intro cover_6_01_016 (And.intro cover_6_01_017 (And.intro cover_6_01_020 (And.intro cover_6_01_021 (And.intro cover_6_01_024 (And.intro cover_6_01_025 (And.intro cover_6_01_032 (And.intro cover_6_01_033 (And.intro cover_6_01_036 (And.intro cover_6_01_037 (And.intro cover_6_01_040 (And.intro cover_6_01_041 (And.intro cover_6_01_048 (And.intro cover_6_01_049 (And.intro cover_6_01_052 (And.intro cover_6_01_053 (And.intro cover_6_01_056 (cover_6_01_057))))))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 1).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 1) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 1).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_01 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_01) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P01
