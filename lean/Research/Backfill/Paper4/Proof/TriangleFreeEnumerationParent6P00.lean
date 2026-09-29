import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P00
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 0).Connected ∧ (reps 6 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 0) (0 : Fin 6)
      (fun v => ([0, 2, 2, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_00_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 5, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 4, 5, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 2, 5, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 1, 5, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 4, 5, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 5, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_007 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 5, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 5, 1, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 5, 4, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 5, 4, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_011 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 5, 4, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 3, 4, 6, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_013 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 3, 4, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_014 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 3, 4, 6, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_015 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 6, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 5, 6, 1, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 5, 6, 4, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 5, 6, 4, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_019 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 5, 6, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 3, 6, 4, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_021 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 3, 6, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_022 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 3, 6, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_023 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 6, 3, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 3, 4, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_025 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 6, 3, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_026 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 6, 3, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_027 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 6, 2, 3, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_028 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 6, 1, 3, 4, 2, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_029 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 1, 2, 3, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_030 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({1, 2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_031 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({0, 1, 2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨53, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 5, 6, 0, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_00_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_00 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {2, 4}, {0, 2, 4}, {1, 2, 4}, {0, 1, 2, 4}, {3, 4}, {0, 3, 4}, {1, 3, 4}, {0, 1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}, {5}]

theorem all_covers_6_00 : neighborhoods_6_00.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 0) S ≃g reps 7 j)) := by
  exact And.intro cover_6_00_001 (And.intro cover_6_00_002 (And.intro cover_6_00_003 (And.intro cover_6_00_004 (And.intro cover_6_00_005 (And.intro cover_6_00_006 (And.intro cover_6_00_007 (And.intro cover_6_00_008 (And.intro cover_6_00_009 (And.intro cover_6_00_010 (And.intro cover_6_00_011 (And.intro cover_6_00_012 (And.intro cover_6_00_013 (And.intro cover_6_00_014 (And.intro cover_6_00_015 (And.intro cover_6_00_016 (And.intro cover_6_00_017 (And.intro cover_6_00_018 (And.intro cover_6_00_019 (And.intro cover_6_00_020 (And.intro cover_6_00_021 (And.intro cover_6_00_022 (And.intro cover_6_00_023 (And.intro cover_6_00_024 (And.intro cover_6_00_025 (And.intro cover_6_00_026 (And.intro cover_6_00_027 (And.intro cover_6_00_028 (And.intro cover_6_00_029 (And.intro cover_6_00_030 (And.intro cover_6_00_031 (cover_6_00_032)))))))))))))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 0).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 0) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 0).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_00) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P00
