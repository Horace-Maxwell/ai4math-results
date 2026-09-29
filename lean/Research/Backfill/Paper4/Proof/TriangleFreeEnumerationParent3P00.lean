import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationParent3P00
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem parent_valid : (reps 3 0).Connected ∧ (reps 3 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 3 0) (0 : Fin 3)
      (fun v => ([0, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem cover_3_00_001 : ∃ j : Fin (repCount 4),
    Nonempty (augment (reps 3 0) ({0} : Finset (Fin 3)) ≃g reps 4 j) := by
  refine ⟨0, ⟨{
    toEquiv := Equiv.ofBijective
      (![3, 0, 1, 2] : Fin 4 → Fin 4) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_3_00_002 : ∃ j : Fin (repCount 4),
    Nonempty (augment (reps 3 0) ({1} : Finset (Fin 3)) ≃g reps 4 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 2] : Fin 4 → Fin 4) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_3_00_004 : ∃ j : Fin (repCount 4),
    Nonempty (augment (reps 3 0) ({2} : Finset (Fin 3)) ≃g reps 4 j) := by
  refine ⟨1, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 3, 1, 2] : Fin 4 → Fin 4) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

theorem cover_3_00_006 : ∃ j : Fin (repCount 4),
    Nonempty (augment (reps 3 0) ({1, 2} : Finset (Fin 3)) ≃g reps 4 j) := by
  refine ⟨2, ⟨{
    toEquiv := Equiv.ofBijective
      (![0, 1, 3, 2] : Fin 4 → Fin 4) (by decide +kernel)
    map_rel_iff' := ?_
  }⟩⟩
  decide +kernel

def neighborhoods_3_00 : List (Finset (Fin 3)) := [{0}, {1}, {2}, {1, 2}]

theorem all_covers_3_00 : neighborhoods_3_00.Forall (fun S => ∃ j : Fin (repCount 4),
    Nonempty (augment (reps 3 0) S ≃g reps 4 j)) := by
  exact And.intro cover_3_00_001 (And.intro cover_3_00_002 (And.intro cover_3_00_004 (cover_3_00_006)))

theorem parent_layer (S : Finset (Fin 3))
    (hne : S.Nonempty) (hi : (reps 3 0).IsIndepSet (S : Set (Fin 3))) :
    ∃ j : Fin (repCount 4), Nonempty (augment (reps 3 0) S ≃g reps 4 j) := by
  have hcover : ∀ T : Finset (Fin 3), T.Nonempty →
      (reps 3 0).IsIndepSet (T : Set (Fin 3)) → T ∈ neighborhoods_3_00 := by
    decide +kernel
  exact (List.forall_iff_forall_mem.mp all_covers_3_00) S (hcover S hne hi)

#print axioms parent_valid
#print axioms parent_layer

end CodexPaper4.TriangleFreeEnumerationParent3P00
