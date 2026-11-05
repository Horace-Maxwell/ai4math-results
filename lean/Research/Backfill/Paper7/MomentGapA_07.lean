import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_07_00
import Research.Backfill.Paper7.MomentGapC_07_01
import Research.Backfill.Paper7.MomentGapC_07_02
import Research.Backfill.Paper7.MomentGapC_07_03

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

def avalues_07 : Fin 4 → ℕ := ![288, 420, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_07

theorem ablock_07 : b4GapABlock 7 = 708 := by
  calc
    b4GapABlock 7 = ∑ i : Fin 4, avalues_07 i := by
      apply b4GapABlock_of_cblocks 7 avalues_07
      intro i
      fin_cases i
      · exact cblock_07_00
      · exact cblock_07_01
      · exact cblock_07_02
      · exact cblock_07_03
    _ = 708 := by decide
#print axioms Paper7MomentGapNumeric.ablock_07

end Paper7MomentGapNumeric
