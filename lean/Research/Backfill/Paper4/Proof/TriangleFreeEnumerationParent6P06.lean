import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P06
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 6).Connected ∧ (reps 6 6).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 6) (0 : Fin 6)
      (fun v => ([0, 2, 1, 1, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_06_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 2, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 4, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 1, 3, 5, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 6, 0, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 6, 2, 0, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨29, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 3, 4, 5, 6, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 2, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 5, 6, 2, 0, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 2, 4, 5, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 2, 5, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_028 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 4, 0, 6, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 6, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 5, 6, 0, 2, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 2, 4, 0, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 2, 0, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_044 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 4, 6, 0, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨38, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 1, 5, 2, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨48, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 1, 5, 2, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 6, 1, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_056 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({3, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 6, 2, 1, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_06_060 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) ({2, 3, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 1, 5, 0, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_06 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {3}, {2, 3}, {4}, {1, 4}, {2, 4}, {3, 4}, {2, 3, 4}, {5}, {1, 5}, {2, 5}, {3, 5}, {2, 3, 5}, {4, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}, {2, 3, 4, 5}]

theorem all_covers_6_06 : neighborhoods_6_06.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 6) S ≃g reps 7 j)) := by
  exact And.intro cover_6_06_001 (And.intro cover_6_06_002 (And.intro cover_6_06_003 (And.intro cover_6_06_004 (And.intro cover_6_06_008 (And.intro cover_6_06_012 (And.intro cover_6_06_016 (And.intro cover_6_06_018 (And.intro cover_6_06_020 (And.intro cover_6_06_024 (And.intro cover_6_06_028 (And.intro cover_6_06_032 (And.intro cover_6_06_034 (And.intro cover_6_06_036 (And.intro cover_6_06_040 (And.intro cover_6_06_044 (And.intro cover_6_06_048 (And.intro cover_6_06_050 (And.intro cover_6_06_052 (And.intro cover_6_06_056 (cover_6_06_060))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 6).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 6) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 6).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_06 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_06) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P06
