import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent5P01
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 5 1).Connected ∧ (reps 5 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 1) (0 : Fin 5)
      (fun v => ([0, 3, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_5_01_001 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({0} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_002 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 2, 0, 1, 3, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_003 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({0, 1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 5, 1, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_004 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 2, 1, 3, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_005 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({0, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 5, 0, 1, 2, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_006 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({1, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨9, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 2, 4, 0, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_007 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({0, 1, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 5, 0, 1, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_008 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 4, 1, 2, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_009 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({0, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 5, 0, 2, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_016 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 1, 2, 0, 3, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_018 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({1, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 2, 4, 0, 3, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_020 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({2, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 4, 2, 0, 3, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_01_022 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) ({1, 2, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 4, 1, 2, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_5_01 : List (Finset (Fin 5)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {4}, {1, 4}, {2, 4}, {1, 2, 4}]

theorem all_covers_5_01 : neighborhoods_5_01.Forall (fun S => ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 1) S ≃g reps 6 j)) := by
  exact And.intro cover_5_01_001 (And.intro cover_5_01_002 (And.intro cover_5_01_003 (And.intro cover_5_01_004 (And.intro cover_5_01_005 (And.intro cover_5_01_006 (And.intro cover_5_01_007 (And.intro cover_5_01_008 (And.intro cover_5_01_009 (And.intro cover_5_01_016 (And.intro cover_5_01_018 (And.intro cover_5_01_020 (cover_5_01_022))))))))))))

theorem parent_layer (S : Finset (Fin 5))
    (hne : S.Nonempty) (hi : (reps 5 1).IsIndepSet (S : Set (Fin 5))) :
    ∃ j : Fin (repCount 6), Nonempty (augment (reps 5 1) S ≃g reps 6 j) := by
  have hcover : ∀ T : Finset (Fin 5), T.Nonempty →
      (reps 5 1).IsIndepSet (T : Set (Fin 5)) → T ∈ neighborhoods_5_01 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_5_01) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent5P01
