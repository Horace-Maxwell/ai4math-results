import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P17
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 17).Connected ∧ (reps 6 17).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 17) (0 : Fin 6)
      (fun v => ([0, 1, 2, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_17_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 2, 3, 4, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 5, 0, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 4, 6, 1, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 1, 0, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨56, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 4, 2, 0, 3, 1, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 1, 0, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 1, 6, 4, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 0, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_021 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({0, 2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 6, 4, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 1, 2, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 2, 1, 3, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_17_042 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) ({1, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 0, 1, 2, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_17 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {0, 4}, {2, 4}, {0, 2, 4}, {5}, {1, 5}, {3, 5}, {1, 3, 5}]

theorem all_covers_6_17 : neighborhoods_6_17.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 17) S ≃g reps 7 j)) := by
  exact And.intro cover_6_17_001 (And.intro cover_6_17_002 (And.intro cover_6_17_004 (And.intro cover_6_17_005 (And.intro cover_6_17_008 (And.intro cover_6_17_009 (And.intro cover_6_17_010 (And.intro cover_6_17_016 (And.intro cover_6_17_017 (And.intro cover_6_17_020 (And.intro cover_6_17_021 (And.intro cover_6_17_032 (And.intro cover_6_17_034 (And.intro cover_6_17_040 (cover_6_17_042))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 17).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 17) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 17).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_17 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_17) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P17
