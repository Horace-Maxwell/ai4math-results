import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapA_00
import Research.Backfill.Paper7.MomentGapA_01
import Research.Backfill.Paper7.MomentGapA_02
import Research.Backfill.Paper7.MomentGapA_03
import Research.Backfill.Paper7.MomentGapA_04
import Research.Backfill.Paper7.MomentGapA_05
import Research.Backfill.Paper7.MomentGapA_06
import Research.Backfill.Paper7.MomentGapA_07
import Research.Backfill.Paper7.MomentGapA_08
import Research.Backfill.Paper7.MomentGapA_09

/-! Generated UNTRUSTED proof-source candidate. Fixed-file flags, native
totals, table completeness and a representative count are not hypotheses.
Every actual row, Q decision, DP cell and complete finite range is checked
by the eventual Lean proofs. Generation alone confers no credit. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentGapNumeric
open Paper7MomentCertificate Paper7MomentCounts Paper7MomentDP
open Paper7MomentReduction Paper7SortedGaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def completeAValues : Fin 10 → ℕ := ![90098, 115838, 96066, 58996, 32972, 12408, 3458, 708, 0, 0]
#print axioms Paper7MomentGapNumeric.completeAValues

theorem candB1_4_41_count : (CandB1 4 41).ncard = 410544 := by
  calc
    (CandB1 4 41).ncard = ∑ i : Fin 10, completeAValues i := by
      apply candB1_b4_ncard_of_ablocks completeAValues
      intro i
      fin_cases i
      · exact ablock_00
      · exact ablock_01
      · exact ablock_02
      · exact ablock_03
      · exact ablock_04
      · exact ablock_05
      · exact ablock_06
      · exact ablock_07
      · exact ablock_08
      · exact ablock_09
    _ = 410544 := by decide
#print axioms Paper7MomentGapNumeric.candB1_4_41_count

theorem complete_gap_sum :
    (∑ g ∈ gapFinset 37, b4RawGapContribution g) = 410544 :=
  candB1_b4_ncard_eq_gap_finset_sum.symm.trans candB1_4_41_count
#print axioms Paper7MomentGapNumeric.complete_gap_sum

end Paper7MomentGapNumeric
