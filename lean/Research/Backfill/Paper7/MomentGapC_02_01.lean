import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_01_00
import Research.Backfill.Paper7.MomentGapD_02_01_01
import Research.Backfill.Paper7.MomentGapD_02_01_02
import Research.Backfill.Paper7.MomentGapD_02_01_03
import Research.Backfill.Paper7.MomentGapD_02_01_04
import Research.Backfill.Paper7.MomentGapD_02_01_05
import Research.Backfill.Paper7.MomentGapD_02_01_06
import Research.Backfill.Paper7.MomentGapD_02_01_07
import Research.Backfill.Paper7.MomentGapD_02_01_08
import Research.Backfill.Paper7.MomentGapD_02_01_09
import Research.Backfill.Paper7.MomentGapD_02_01_10
import Research.Backfill.Paper7.MomentGapD_02_01_11
import Research.Backfill.Paper7.MomentGapD_02_01_12
import Research.Backfill.Paper7.MomentGapD_02_01_13

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

def cvalues_02_01 : Fin 14 → ℕ := ![2176, 4092, 2616, 4008, 4368, 4008, 3360, 5352, 1008, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_01

theorem cblock_02_01 : b4GapCBlock 2 1 = 30988 := by
  calc
    b4GapCBlock 2 1 = ∑ i : Fin 14, cvalues_02_01 i := by
      apply b4GapCBlock_of_dblocks 2 1 cvalues_02_01
      intro i
      fin_cases i
      · exact dblock_02_01_00
      · exact dblock_02_01_01
      · exact dblock_02_01_02
      · exact dblock_02_01_03
      · exact dblock_02_01_04
      · exact dblock_02_01_05
      · exact dblock_02_01_06
      · exact dblock_02_01_07
      · exact dblock_02_01_08
      · exact dblock_02_01_09
      · exact dblock_02_01_10
      · exact dblock_02_01_11
      · exact dblock_02_01_12
      · exact dblock_02_01_13
    _ = 30988 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_01

end Paper7MomentGapNumeric
