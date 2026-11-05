import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_01_07_00
import Research.Backfill.Paper7.MomentGapD_01_07_01
import Research.Backfill.Paper7.MomentGapD_01_07_02
import Research.Backfill.Paper7.MomentGapD_01_07_03
import Research.Backfill.Paper7.MomentGapD_01_07_04
import Research.Backfill.Paper7.MomentGapD_01_07_05
import Research.Backfill.Paper7.MomentGapD_01_07_06

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

def cvalues_01_07 : Fin 7 → ℕ := ![1356, 972, 600, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_01_07

theorem cblock_01_07 : b4GapCBlock 1 7 = 2928 := by
  calc
    b4GapCBlock 1 7 = ∑ i : Fin 7, cvalues_01_07 i := by
      apply b4GapCBlock_of_dblocks 1 7 cvalues_01_07
      intro i
      fin_cases i
      · exact dblock_01_07_00
      · exact dblock_01_07_01
      · exact dblock_01_07_02
      · exact dblock_01_07_03
      · exact dblock_01_07_04
      · exact dblock_01_07_05
      · exact dblock_01_07_06
    _ = 2928 := by decide
#print axioms Paper7MomentGapNumeric.cblock_01_07

end Paper7MomentGapNumeric
