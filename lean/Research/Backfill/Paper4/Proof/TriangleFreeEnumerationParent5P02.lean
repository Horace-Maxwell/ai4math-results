import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent5P02
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 5 2).Connected ∧ (reps 5 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 2) (0 : Fin 5)
      (fun v => ([0, 1, 2, 3, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_5_02_001 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({0} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 0, 5, 1, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_002 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 5, 4, 0] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_004 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨4, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 3, 1, 5, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_005 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({0, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨8, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 4, 2, 0, 1, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_008 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 4, 3, 1, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_009 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({0, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 4, 3, 5, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_010 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({1, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨9, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 1, 3, 5, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_016 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 5, 0, 1, 3, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_018 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({1, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨9, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 4, 0, 5, 3, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_020 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({2, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨10, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 1, 5, 3, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_024 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({3, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨11, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 5, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_02_026 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) ({1, 3, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 5, 4, 2, 3] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_5_02 : List (Finset (Fin 5)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {1, 4}, {2, 4}, {3, 4}, {1, 3, 4}]

theorem all_covers_5_02 : neighborhoods_5_02.Forall (fun S => ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 2) S ≃g reps 6 j)) := by
  exact And.intro cover_5_02_001 (And.intro cover_5_02_002 (And.intro cover_5_02_004 (And.intro cover_5_02_005 (And.intro cover_5_02_008 (And.intro cover_5_02_009 (And.intro cover_5_02_010 (And.intro cover_5_02_016 (And.intro cover_5_02_018 (And.intro cover_5_02_020 (And.intro cover_5_02_024 (cover_5_02_026)))))))))))

theorem parent_layer (S : Finset (Fin 5))
    (hne : S.Nonempty) (hi : (reps 5 2).IsIndepSet (S : Set (Fin 5))) :
    ∃ j : Fin (repCount 6), Nonempty (augment (reps 5 2) S ≃g reps 6 j) := by
  have hcover : ∀ T : Finset (Fin 5), T.Nonempty →
      (reps 5 2).IsIndepSet (T : Set (Fin 5)) → T ∈ neighborhoods_5_02 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_5_02) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent5P02
