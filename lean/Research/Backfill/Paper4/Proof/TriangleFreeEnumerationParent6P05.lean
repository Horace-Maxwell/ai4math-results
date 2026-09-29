import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P05
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 5).Connected ∧ (reps 6 5).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 5) (0 : Fin 6)
      (fun v => ([0, 1, 4, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_05_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨8, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 0, 3, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 5, 4, 3, 2, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 4, 3, 2, 1, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨22, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 0, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨25, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 4, 5, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨8, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 5, 2, 4, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨20, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 4, 5, 6, 3, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨22, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 1, 2, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 4, 1, 3, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨19, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 6, 4, 1, 0, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨24, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 6, 1, 4, 0, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨23, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 0, 3, 1, 2, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_021 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({0, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 5, 6, 2, 3, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_022 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 6, 5, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 2, 6, 3, 1, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨23, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 5, 6, 2, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨24, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 1, 6, 3, 2, 0, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_038 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨39, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 1, 0, 4, 5, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨19, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 6, 3, 2, 0, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_05_042 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) ({1, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 0, 4, 3, 2, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_05 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {1, 2}, {3}, {0, 3}, {1, 3}, {4}, {0, 4}, {1, 4}, {2, 4}, {0, 2, 4}, {1, 2, 4}, {5}, {1, 5}, {2, 5}, {1, 2, 5}, {3, 5}, {1, 3, 5}]

theorem all_covers_6_05 : neighborhoods_6_05.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 5) S ≃g reps 7 j)) := by
  exact And.intro cover_6_05_001 (And.intro cover_6_05_002 (And.intro cover_6_05_004 (And.intro cover_6_05_005 (And.intro cover_6_05_006 (And.intro cover_6_05_008 (And.intro cover_6_05_009 (And.intro cover_6_05_010 (And.intro cover_6_05_016 (And.intro cover_6_05_017 (And.intro cover_6_05_018 (And.intro cover_6_05_020 (And.intro cover_6_05_021 (And.intro cover_6_05_022 (And.intro cover_6_05_032 (And.intro cover_6_05_034 (And.intro cover_6_05_036 (And.intro cover_6_05_038 (And.intro cover_6_05_040 (cover_6_05_042)))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 5).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 5) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 5).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_05 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_05) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P05
