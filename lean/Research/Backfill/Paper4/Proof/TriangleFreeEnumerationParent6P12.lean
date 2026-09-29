import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P12
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 12).Connected ∧ (reps 6 12).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 12) (0 : Fin 6)
      (fun v => ([0, 2, 1, 2, 3, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_12_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨33, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 4, 1, 3, 2, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 2, 4, 0, 3, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 1, 0, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨26, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 1, 2, 3, 0, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 4, 2, 3, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 5, 2, 0, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 4, 1, 0, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_011 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 4, 3, 0, 5, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨27, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 3, 1, 4, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨46, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 2, 1, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 4, 1, 5, 2, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 4, 1, 3, 2, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 5, 4, 0, 2, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 0, 1, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_035 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 4, 5, 0, 3, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_040 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 5, 2, 1, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_041 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 4, 2, 0, 3, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_042 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({1, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨52, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 0, 3, 2, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_12_043 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) ({0, 1, 3, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 3, 2, 1, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_12 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {4}, {0, 4}, {2, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {3, 5}, {0, 3, 5}, {1, 3, 5}, {0, 1, 3, 5}]

theorem all_covers_6_12 : neighborhoods_6_12.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 12) S ≃g reps 7 j)) := by
  exact And.intro cover_6_12_001 (And.intro cover_6_12_002 (And.intro cover_6_12_003 (And.intro cover_6_12_004 (And.intro cover_6_12_008 (And.intro cover_6_12_009 (And.intro cover_6_12_010 (And.intro cover_6_12_011 (And.intro cover_6_12_016 (And.intro cover_6_12_017 (And.intro cover_6_12_020 (And.intro cover_6_12_032 (And.intro cover_6_12_033 (And.intro cover_6_12_034 (And.intro cover_6_12_035 (And.intro cover_6_12_040 (And.intro cover_6_12_041 (And.intro cover_6_12_042 (cover_6_12_043))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 12).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 12) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 12).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_12 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_12) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P12
