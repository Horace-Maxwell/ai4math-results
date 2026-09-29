import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent5P03
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 5 3).Connected ∧ (reps 5 3).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 3) (0 : Fin 5)
      (fun v => ([0, 1, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_5_03_001 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({0} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨9, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 4, 3, 1, 2, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_002 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({1} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨6, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 1, 2, 3, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_004 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨8, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 3, 4, 5, 1] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_005 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({0, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 5, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_006 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({1, 2} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨12, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 4, 1, 3, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_008 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 1, 3, 2, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_009 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({0, 3} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 4, 3, 5, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_016 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![4, 0, 1, 2, 3, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_017 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({0, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 4, 5, 3, 2] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_024 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({3, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 3, 1, 5, 4] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_5_03_025 : ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) ({0, 3, 4} : Finset (Fin 5)) ≃g reps 6 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 2, 4, 5] : Fin 6 → Fin 6) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_5_03 : List (Finset (Fin 5)) := [{0}, {1}, {2}, {0, 2}, {1, 2}, {3}, {0, 3}, {4}, {0, 4}, {3, 4}, {0, 3, 4}]

theorem all_covers_5_03 : neighborhoods_5_03.Forall (fun S => ∃ j : Fin (repCount 6),
    Nonempty (augment (reps 5 3) S ≃g reps 6 j)) := by
  exact And.intro cover_5_03_001 (And.intro cover_5_03_002 (And.intro cover_5_03_004 (And.intro cover_5_03_005 (And.intro cover_5_03_006 (And.intro cover_5_03_008 (And.intro cover_5_03_009 (And.intro cover_5_03_016 (And.intro cover_5_03_017 (And.intro cover_5_03_024 (cover_5_03_025))))))))))

theorem parent_layer (S : Finset (Fin 5))
    (hne : S.Nonempty) (hi : (reps 5 3).IsIndepSet (S : Set (Fin 5))) :
    ∃ j : Fin (repCount 6), Nonempty (augment (reps 5 3) S ≃g reps 6 j) := by
  have hcover : ∀ T : Finset (Fin 5), T.Nonempty →
      (reps 5 3).IsIndepSet (T : Set (Fin 5)) → T ∈ neighborhoods_5_03 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_5_03) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent5P03
