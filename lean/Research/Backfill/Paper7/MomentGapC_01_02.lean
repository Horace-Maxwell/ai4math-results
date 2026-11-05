import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_01_02_00
import Research.Backfill.Paper7.MomentGapD_01_02_01
import Research.Backfill.Paper7.MomentGapD_01_02_02
import Research.Backfill.Paper7.MomentGapD_01_02_03
import Research.Backfill.Paper7.MomentGapD_01_02_04
import Research.Backfill.Paper7.MomentGapD_01_02_05
import Research.Backfill.Paper7.MomentGapD_01_02_06
import Research.Backfill.Paper7.MomentGapD_01_02_07
import Research.Backfill.Paper7.MomentGapD_01_02_08
import Research.Backfill.Paper7.MomentGapD_01_02_09
import Research.Backfill.Paper7.MomentGapD_01_02_10
import Research.Backfill.Paper7.MomentGapD_01_02_11
import Research.Backfill.Paper7.MomentGapD_01_02_12
import Research.Backfill.Paper7.MomentGapD_01_02_13

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

def cvalues_01_02 : Fin 14 → ℕ := ![1752, 3072, 3312, 2088, 4800, 1704, 2592, 2880, 1344, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_01_02

theorem cblock_01_02 : b4GapCBlock 1 2 = 23544 := by
  calc
    b4GapCBlock 1 2 = ∑ i : Fin 14, cvalues_01_02 i := by
      apply b4GapCBlock_of_dblocks 1 2 cvalues_01_02
      intro i
      fin_cases i
      · exact dblock_01_02_00
      · exact dblock_01_02_01
      · exact dblock_01_02_02
      · exact dblock_01_02_03
      · exact dblock_01_02_04
      · exact dblock_01_02_05
      · exact dblock_01_02_06
      · exact dblock_01_02_07
      · exact dblock_01_02_08
      · exact dblock_01_02_09
      · exact dblock_01_02_10
      · exact dblock_01_02_11
      · exact dblock_01_02_12
      · exact dblock_01_02_13
    _ = 23544 := by decide
#print axioms Paper7MomentGapNumeric.cblock_01_02

end Paper7MomentGapNumeric
