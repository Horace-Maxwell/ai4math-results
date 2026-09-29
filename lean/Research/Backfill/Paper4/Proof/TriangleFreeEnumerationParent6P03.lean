import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P03
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 3).Connected ∧ (reps 6 3).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 3) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_03_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨9, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 3, 4, 6, 5, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨3, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 4, 6, 5, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 2, 4, 5, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 1, 3, 0, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨5, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 1, 4, 2, 0, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨17, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 3, 1, 4, 0, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨14, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 1, 3, 4, 6, 5, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_013 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨30, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 3, 0, 2, 6, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 4, 6, 5, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨24, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 5, 4, 6, 1, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_018 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({1, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 3, 2, 0, 5, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 1, 5, 0, 6, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_025 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 3, 4, 6, 0, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨7, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 4, 3, 5, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨24, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 0, 4, 5, 1, 6, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨15, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 2, 3, 5, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_036 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨18, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 2, 5, 1, 6, 0, 4] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_037 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 2, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨35, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 4, 3, 0, 6, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨22, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 6, 5, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_049 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({0, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨41, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 1, 5, 2, 4, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_03_050 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) ({1, 4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨31, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 4, 5, 3, 6, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_03 : List (Finset (Fin 6)) := [{0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {2, 3}, {0, 2, 3}, {4}, {0, 4}, {1, 4}, {3, 4}, {0, 3, 4}, {5}, {0, 5}, {1, 5}, {2, 5}, {0, 2, 5}, {4, 5}, {0, 4, 5}, {1, 4, 5}]

theorem all_covers_6_03 : neighborhoods_6_03.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 3) S ≃g reps 7 j)) := by
  exact And.intro cover_6_03_001 (And.intro cover_6_03_002 (And.intro cover_6_03_004 (And.intro cover_6_03_005 (And.intro cover_6_03_008 (And.intro cover_6_03_009 (And.intro cover_6_03_012 (And.intro cover_6_03_013 (And.intro cover_6_03_016 (And.intro cover_6_03_017 (And.intro cover_6_03_018 (And.intro cover_6_03_024 (And.intro cover_6_03_025 (And.intro cover_6_03_032 (And.intro cover_6_03_033 (And.intro cover_6_03_034 (And.intro cover_6_03_036 (And.intro cover_6_03_037 (And.intro cover_6_03_048 (And.intro cover_6_03_049 (cover_6_03_050))))))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 3).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 3) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 3).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_03 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_03) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P03
