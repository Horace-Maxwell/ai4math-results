import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P04
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 4).Connected ∧ (reps 6 4).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 4) (0 : Fin 6)
      (fun v => ([0, 3, 3, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_04_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 6, 2, 1, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 4, 0, 1, 3, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨20, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 6, 4, 5, 0, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 4, 1, 3, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨20, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 6, 5, 0, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨23, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 4, 1, 2, 5, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_007 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({0, 1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 4, 2, 3, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 3, 1, 2, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 6, 2, 3, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 6, 2, 1, 0, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 5, 0, 1, 2, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 5, 1, 2, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_022 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨37, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 1, 3, 2, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨8, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 6, 2, 4, 3, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨22, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 5, 1, 2, 6, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨22, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 5, 2, 6, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_038 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨40, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 6, 1, 2, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨16, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 4, 0, 2, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨21, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 5, 6, 2, 1, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 0, 4, 1, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 3, 4, 1, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_04_054 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) ({1, 2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 4, 0, 2, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_04 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {4}, {1, 4}, {2, 4}, {1, 2, 4}, {5}, {1, 5}, {2, 5}, {1, 2, 5}, {3, 5}, {4, 5}, {1, 4, 5}, {2, 4, 5}, {1, 2, 4, 5}]

theorem all_covers_6_04 : neighborhoods_6_04.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 4) S ≃g reps 7 j)) := by
  exact And.intro cover_6_04_001 (And.intro cover_6_04_002 (And.intro cover_6_04_003 (And.intro cover_6_04_004 (And.intro cover_6_04_005 (And.intro cover_6_04_006 (And.intro cover_6_04_007 (And.intro cover_6_04_008 (And.intro cover_6_04_009 (And.intro cover_6_04_016 (And.intro cover_6_04_018 (And.intro cover_6_04_020 (And.intro cover_6_04_022 (And.intro cover_6_04_032 (And.intro cover_6_04_034 (And.intro cover_6_04_036 (And.intro cover_6_04_038 (And.intro cover_6_04_040 (And.intro cover_6_04_048 (And.intro cover_6_04_050 (And.intro cover_6_04_052 (cover_6_04_054)))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 4).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 4) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 4).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_04 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_04) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P04
