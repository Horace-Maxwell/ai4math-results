import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent6P16
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 6 16).Connected ∧ (reps 6 16).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 16) (0 : Fin 6)
      (fun v => ([0, 2, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_6_16_001 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_002 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_003 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 1} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 5, 0, 6, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_004 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 1, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_005 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 5, 6, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_006 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 5, 6, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_007 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 1, 2} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 5, 6, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_008 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨43, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 3, 1, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_009 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 0, 6, 5, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_010 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 6, 5, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_011 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 1, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 2, 6, 5, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_012 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨54, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 1, 5, 3, 4, 2] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_013 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 6, 2, 5, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_014 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({1, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨57, ⟨{
    toEquiv := Equiv.ofBijective
      (![6, 0, 2, 5, 3, 4, 1] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_015 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({0, 1, 2, 3} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨58, ⟨{
    toEquiv := Equiv.ofBijective
      (![1, 2, 4, 5, 0, 3, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_016 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({4} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_032 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨42, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 2, 3, 5, 4, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_6_16_048 : ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) ({4, 5} : Finset (Fin 6)) ≃g reps 7 j) := by
  refine ⟨53, ⟨{
    toEquiv := Equiv.ofBijective
      (![2, 3, 4, 5, 0, 1, 6] : Fin 7 → Fin 7) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_6_16 : List (Finset (Fin 6)) := [{0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {4}, {5}, {4, 5}]

theorem all_covers_6_16 : neighborhoods_6_16.Forall (fun S => ∃ j : Fin (repCount 7),
    Nonempty (augment (reps 6 16) S ≃g reps 7 j)) := by
  exact And.intro cover_6_16_001 (And.intro cover_6_16_002 (And.intro cover_6_16_003 (And.intro cover_6_16_004 (And.intro cover_6_16_005 (And.intro cover_6_16_006 (And.intro cover_6_16_007 (And.intro cover_6_16_008 (And.intro cover_6_16_009 (And.intro cover_6_16_010 (And.intro cover_6_16_011 (And.intro cover_6_16_012 (And.intro cover_6_16_013 (And.intro cover_6_16_014 (And.intro cover_6_16_015 (And.intro cover_6_16_016 (And.intro cover_6_16_032 (cover_6_16_048)))))))))))))))))

theorem parent_layer (S : Finset (Fin 6))
    (hne : S.Nonempty) (hi : (reps 6 16).IsIndepSet (S : Set (Fin 6))) :
    ∃ j : Fin (repCount 7), Nonempty (augment (reps 6 16) S ≃g reps 7 j) := by
  have hcover : ∀ T : Finset (Fin 6), T.Nonempty →
      (reps 6 16).IsIndepSet (T : Set (Fin 6)) → T ∈ neighborhoods_6_16 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_6_16) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent6P16
