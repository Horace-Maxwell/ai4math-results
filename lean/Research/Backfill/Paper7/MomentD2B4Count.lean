import Research.Backfill.Paper7.MomentBudgetEncoding
import Research.Backfill.Paper7.MomentB4GapNumericComplete

/-! The labelled D2(4,41) clause of the original LegacyMomentCounts.
The existing even-cycle labelled-cardinality bridge is reused. This module
does not identify either canonical representative convention or assume a
candidate table complete. The two declarations are uncompiled candidates.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentD2Numeric
open BackfillPaper7.Challenge.Legacy

theorem candD2_4_41_count : (CandD2 4 41).ncard = 410544 :=
  (Paper7MomentCounts.candD2_ncard_eq_candB1_of_even 4 41 ⟨2, rfl⟩).trans
    Paper7MomentGapNumeric.candB1_4_41_count
#print axioms Paper7MomentD2Numeric.candD2_4_41_count

theorem candD2_4_41_finite_count :
    (CandD2 4 41).Finite ∧ (CandD2 4 41).ncard = 410544 :=
  ⟨Paper7MomentCounts.candD2_finite 4 41, candD2_4_41_count⟩
#print axioms Paper7MomentD2Numeric.candD2_4_41_finite_count

end Paper7MomentD2Numeric
