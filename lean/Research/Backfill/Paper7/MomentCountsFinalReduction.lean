import Research.Backfill.Paper7.MomentB4CompleteCounts
import Research.Backfill.Paper7.MomentD2B4Count
import Research.Backfill.Paper7.MomentB6BasicFixedTransport
import Research.Backfill.Paper7.MomentB6ThreePairAction
import Research.Backfill.Paper7.MomentB6Type1122CertifiedTotal

/-! SOURCE ONLY. Reduction of the unchanged complete LegacyMomentCounts
contract to its one still unresolved labelled six-circle count.
The four b=4 clauses, all eight finiteness assertions, the b=6 D2 labelled
clause and both b=6 canonical clauses are retained. The reflected Value
13231 comes from the actual932 checked total; the three-pair count 129
comes from actual889. No cardinality is added as a premise to the original
contract, and no new numerical evaluation or complete-contract proof is
claimed by this equivalence. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge.Legacy
open Paper7MomentCanonicalNumeric Paper7MomentCanonicalSix

/-- All original sixteen conjuncts are equivalent to the remaining original
labelled count. The reverse implication derives its other clauses internally. -/
theorem legacyMomentCounts_iff_b6_labelled_count :
    LegacyMomentCounts ↔ (CandB1 6 42).ncard = 14215675 := by
  constructor
  · rintro ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  · intro hL
    have hF : b6FixedCount (b6Reflection 0) = 13231 :=
      b6_reflection_zero_count_eq_totalValue.trans
        (show b6R1122TotalValue = 13231 from rfl)
    have hBurnside := b6_canonB1_two_remaining_fixed_types
    rw [hL, b6_rotation_three_fixed_count, hF] at hBurnside
    have hCanonB1 : (canonB1 6 42).ncard = 1187991 := by
      omega
    have hD2 : (CandD2 6 42).ncard = 14215675 :=
      (candD2_ncard_eq_candB1_of_even 6 42 ⟨3, rfl⟩).trans hL
    have hCanonD2 : (canonD2 6 42).ncard = 1187991 :=
      (canonB1_ncard_eq_canonD2 6 42 (by decide) (by decide) ⟨3, rfl⟩).symm.trans
        hCanonB1
    exact ⟨candB1_finite 4 41, Paper7MomentGapNumeric.candB1_4_41_count,
      canonB1_b4_original_finite, canonB1_b4_original_ncard,
      Paper7MomentD2Numeric.candD2_4_41_finite_count.1,
      Paper7MomentD2Numeric.candD2_4_41_finite_count.2,
      canonD2_b4_original_finite, canonD2_b4_original_ncard,
      candB1_finite 6 42, hL, canonB1_finite 6 42, hCanonB1,
      candD2_finite 6 42, hD2, canonD2_finite 6 42, hCanonD2⟩

#print axioms Paper7MomentCounts.legacyMomentCounts_iff_b6_labelled_count

end Paper7MomentCounts
