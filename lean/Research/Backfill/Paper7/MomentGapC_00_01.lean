import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_01_00
import Research.Backfill.Paper7.MomentGapD_00_01_01
import Research.Backfill.Paper7.MomentGapD_00_01_02
import Research.Backfill.Paper7.MomentGapD_00_01_03
import Research.Backfill.Paper7.MomentGapD_00_01_04
import Research.Backfill.Paper7.MomentGapD_00_01_05
import Research.Backfill.Paper7.MomentGapD_00_01_06
import Research.Backfill.Paper7.MomentGapD_00_01_07
import Research.Backfill.Paper7.MomentGapD_00_01_08
import Research.Backfill.Paper7.MomentGapD_00_01_09
import Research.Backfill.Paper7.MomentGapD_00_01_10
import Research.Backfill.Paper7.MomentGapD_00_01_11
import Research.Backfill.Paper7.MomentGapD_00_01_12
import Research.Backfill.Paper7.MomentGapD_00_01_13
import Research.Backfill.Paper7.MomentGapD_00_01_14
import Research.Backfill.Paper7.MomentGapD_00_01_15
import Research.Backfill.Paper7.MomentGapD_00_01_16
import Research.Backfill.Paper7.MomentGapD_00_01_17

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

def cvalues_00_01 : Fin 18 → ℕ := ![288, 840, 1128, 1284, 1344, 1872, 1440, 1944, 1572, 504, 612, 252, 24, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_01

theorem cblock_00_01 : b4GapCBlock 0 1 = 13104 := by
  calc
    b4GapCBlock 0 1 = ∑ i : Fin 18, cvalues_00_01 i := by
      apply b4GapCBlock_of_dblocks 0 1 cvalues_00_01
      intro i
      fin_cases i
      · exact dblock_00_01_00
      · exact dblock_00_01_01
      · exact dblock_00_01_02
      · exact dblock_00_01_03
      · exact dblock_00_01_04
      · exact dblock_00_01_05
      · exact dblock_00_01_06
      · exact dblock_00_01_07
      · exact dblock_00_01_08
      · exact dblock_00_01_09
      · exact dblock_00_01_10
      · exact dblock_00_01_11
      · exact dblock_00_01_12
      · exact dblock_00_01_13
      · exact dblock_00_01_14
      · exact dblock_00_01_15
      · exact dblock_00_01_16
      · exact dblock_00_01_17
    _ = 13104 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_01

end Paper7MomentGapNumeric
