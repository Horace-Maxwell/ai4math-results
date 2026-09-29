import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P13
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 13).Connected ∧ (reps 6 13).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 13) (0 : Fin 6)
      (fun v => ([0, 2, 1, 3, 3, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_13_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨37, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 0, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 4, 2, 0, 1, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 5, 2, 1, 4, 0, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨29, ⟨{
    toEquiv := Equiv.ofBijective
      (![5, 3, 2, 0, 1, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨30, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 0, 2, 1, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨50, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 3, 4, 1, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 1, 3, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨30, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 0, 1, 2, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_017 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨50, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 3, 1, 4, 2, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_020 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({2, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨44, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 2, 5, 3, 1, 4, 0] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_024 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨45, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 0, 2, 4, 5, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_025 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨56, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 0, 2, 4, 5, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_028 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({2, 3, 4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨52, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 1, 0, 2, 4, 3, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨28, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 3, 2, 0, 1, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_033 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨47, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 2, 1, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_034 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 4, 1, 0, 2, 5, 3] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_13_035 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) ({0, 1, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 1, 0, 6, 4, 5] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_13 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {3}, {0, 3}, {2, 3}, {4}, {0, 4}, {2, 4}, {3, 4}, {0, 3, 4}, {2, 3, 4}, {5}, {0, 5}, {1, 5}, {0, 1, 5}]

theorem all_covers_6_13 : neighborhoods_6_13.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 13) S ≃g reps 7 j)) := by
  exact And.intro cover_6_13_001 (And.intro cover_6_13_002 (And.intro cover_6_13_003 (And.intro cover_6_13_004 (And.intro cover_6_13_008 (And.intro cover_6_13_009 (And.intro cover_6_13_012 (And.intro cover_6_13_016 (And.intro cover_6_13_017 (And.intro cover_6_13_020 (And.intro cover_6_13_024 (And.intro cover_6_13_025 (And.intro cover_6_13_028 (And.intro cover_6_13_032 (And.intro cover_6_13_033 (And.intro cover_6_13_034 (cover_6_13_035))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 13).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 13) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 13).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_13 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_13) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P13
