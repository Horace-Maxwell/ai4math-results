import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P02
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 2).Connected ∧ (reps 6 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 2) (0 : Fin 6)
      (fun v => ([0, 1, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_02_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 2, 5, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 3, 2, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 2, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨21, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 4, 2, 5, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 1, 0, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 1, 5, 0, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 5, 0, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_014 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨29, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 1, 2, 5, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 1, 4, 3, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 4, 2, 3, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 5, 4, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 1, 5, 4, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_022 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 4, 0, 3, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 1, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 4, 2, 1, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 5, 6, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 1, 5, 6, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_038 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 4, 0, 6, 3, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨21, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 1, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_049 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({0, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨29, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 5, 6, 3, 0, 1, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 6, 5, 1, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_052 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨36, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 3, 5, 1, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_02_054 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) ({1, 2, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨48, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 1, 5, 3, 2, 6, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_02 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3}, {4}, {0, 4}, {1, 4}, {2, 4}, {1, 2, 4}, {5}, {0, 5}, {1, 5}, {2, 5}, {1, 2, 5}, {4, 5}, {0, 4, 5}, {1, 4, 5}, {2, 4, 5}, {1, 2, 4, 5}]

theorem all_covers_6_02 : neighborhoods_6_02.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 2) S ≃g reps 7 j)) := by
  exact And.intro cover_6_02_001 (And.intro cover_6_02_002 (And.intro cover_6_02_004 (And.intro cover_6_02_006 (And.intro cover_6_02_008 (And.intro cover_6_02_010 (And.intro cover_6_02_012 (And.intro cover_6_02_014 (And.intro cover_6_02_016 (And.intro cover_6_02_017 (And.intro cover_6_02_018 (And.intro cover_6_02_020 (And.intro cover_6_02_022 (And.intro cover_6_02_032 (And.intro cover_6_02_033 (And.intro cover_6_02_034 (And.intro cover_6_02_036 (And.intro cover_6_02_038 (And.intro cover_6_02_048 (And.intro cover_6_02_049 (And.intro cover_6_02_050 (And.intro cover_6_02_052 (cover_6_02_054))))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 2).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 2) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 2).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_02 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_02) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P02
