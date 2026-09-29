import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P08
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 8).Connected ∧ (reps 6 8).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 8) (0 : Fin 6)
      (fun v => ([0, 4, 1, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_08_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨19, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 6, 0, 3, 2, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨19, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 3, 0, 2, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨40, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 4, 1, 5, 0, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 0, 2, 1, 3, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 1, 4, 5, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨13, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 5, 1, 2, 3, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨32, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 4, 1, 5, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨27, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 3, 4, 0, 1, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 3, 4, 1, 0, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 2, 4, 1, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 4, 2, 1, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_019 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨51, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 0, 4, 6, 5, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 3, 4, 0, 1, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 2, 4, 3, 1, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨34, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 4, 2, 3, 1, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_035 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨51, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 0, 4, 5, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨30, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 5, 0, 2, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_049 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 6, 2, 0, 1, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 0, 2, 1, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_08_051 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) ({0, 1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨55, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 6, 0, 1, 2, 3, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_08 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {1, 2}, {3}, {0, 3}, {2, 3}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}, {4, 5}, {0, 4, 5}, {1, 4, 5}, {0, 1, 4, 5}]

theorem all_covers_6_08 : neighborhoods_6_08.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 8) S ≃g reps 7 j)) := by
  exact And.intro cover_6_08_001 (And.intro cover_6_08_002 (And.intro cover_6_08_003 (And.intro cover_6_08_004 (And.intro cover_6_08_006 (And.intro cover_6_08_008 (And.intro cover_6_08_009 (And.intro cover_6_08_012 (And.intro cover_6_08_016 (And.intro cover_6_08_017 (And.intro cover_6_08_018 (And.intro cover_6_08_019 (And.intro cover_6_08_032 (And.intro cover_6_08_033 (And.intro cover_6_08_034 (And.intro cover_6_08_035 (And.intro cover_6_08_048 (And.intro cover_6_08_049 (And.intro cover_6_08_050 (cover_6_08_051)))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 8).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 8) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 8).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_08 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_08) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P08
