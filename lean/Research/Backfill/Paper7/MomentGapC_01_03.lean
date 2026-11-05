import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_01_03_00
import Research.Backfill.Paper7.MomentGapD_01_03_01
import Research.Backfill.Paper7.MomentGapD_01_03_02
import Research.Backfill.Paper7.MomentGapD_01_03_03
import Research.Backfill.Paper7.MomentGapD_01_03_04
import Research.Backfill.Paper7.MomentGapD_01_03_05
import Research.Backfill.Paper7.MomentGapD_01_03_06
import Research.Backfill.Paper7.MomentGapD_01_03_07
import Research.Backfill.Paper7.MomentGapD_01_03_08
import Research.Backfill.Paper7.MomentGapD_01_03_09
import Research.Backfill.Paper7.MomentGapD_01_03_10
import Research.Backfill.Paper7.MomentGapD_01_03_11
import Research.Backfill.Paper7.MomentGapD_01_03_12

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

def cvalues_01_03 : Fin 13 → ℕ := ![1752, 1536, 3048, 1416, 4632, 1800, 2940, 2184, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_01_03

theorem cblock_01_03 : b4GapCBlock 1 3 = 19308 := by
  calc
    b4GapCBlock 1 3 = ∑ i : Fin 13, cvalues_01_03 i := by
      apply b4GapCBlock_of_dblocks 1 3 cvalues_01_03
      intro i
      fin_cases i
      · exact dblock_01_03_00
      · exact dblock_01_03_01
      · exact dblock_01_03_02
      · exact dblock_01_03_03
      · exact dblock_01_03_04
      · exact dblock_01_03_05
      · exact dblock_01_03_06
      · exact dblock_01_03_07
      · exact dblock_01_03_08
      · exact dblock_01_03_09
      · exact dblock_01_03_10
      · exact dblock_01_03_11
      · exact dblock_01_03_12
    _ = 19308 := by decide
#print axioms Paper7MomentGapNumeric.cblock_01_03

end Paper7MomentGapNumeric
