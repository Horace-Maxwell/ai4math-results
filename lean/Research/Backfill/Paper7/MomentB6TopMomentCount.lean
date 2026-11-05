import Research.Backfill.Paper7.MomentB6TopMomentRows

/-! Uncompiled exact labelled top-moment fibre cardinalities.  The two
original candidate predicates are transported separately.  No canonical
orbit count, full labelled total, or identity of canonical sets is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

def b6TopMomentGuardEquiv :
    Fin 6 ≃ {x : PQ 6 // b6CandidateGuard x ∧ theta x = 1272} :=
  Equiv.ofBijective
    (fun i => ⟨b6TopMomentRow i, b6TopMomentRow_guard i,
      (b6TopMomentRow_features i).2.2⟩)
    ⟨fun _ _ h => b6TopMomentRow_injective (congrArg Subtype.val h), by
      intro x
      obtain ⟨i, hi⟩ := (b6_top_moment_guard_iff x.val).mp x.property
      exact ⟨i, Subtype.ext hi.symm⟩⟩
#print axioms Paper7MomentCounts.b6TopMomentGuardEquiv

def b6TopMomentB1Equiv :
    Fin 6 ≃ {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 1272} :=
  b6TopMomentGuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candB1_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6TopMomentB1Equiv

def b6TopMomentD2Equiv :
    Fin 6 ≃ {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 1272} :=
  b6TopMomentGuardEquiv.trans (Equiv.subtypeEquivRight
    (fun x => and_congr (b6_candD2_iff_guard x).symm Iff.rfl))
#print axioms Paper7MomentCounts.b6TopMomentD2Equiv

theorem b6_top_moment_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 1272}.ncard = 6 := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42 ∧ theta x = 1272} = 6
  rw [Nat.card_congr b6TopMomentB1Equiv.symm]
  simp
#print axioms Paper7MomentCounts.b6_top_moment_candB1_ncard

theorem b6_top_moment_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 1272}.ncard = 6 := by
  change Nat.card {x : PQ 6 // x ∈ CandD2 6 42 ∧ theta x = 1272} = 6
  rw [Nat.card_congr b6TopMomentD2Equiv.symm]
  simp
#print axioms Paper7MomentCounts.b6_top_moment_candD2_ncard

end Paper7MomentCounts
