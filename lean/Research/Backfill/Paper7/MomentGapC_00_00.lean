import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_00_00
import Research.Backfill.Paper7.MomentGapD_00_00_01
import Research.Backfill.Paper7.MomentGapD_00_00_02
import Research.Backfill.Paper7.MomentGapD_00_00_03
import Research.Backfill.Paper7.MomentGapD_00_00_04
import Research.Backfill.Paper7.MomentGapD_00_00_05
import Research.Backfill.Paper7.MomentGapD_00_00_06
import Research.Backfill.Paper7.MomentGapD_00_00_07
import Research.Backfill.Paper7.MomentGapD_00_00_08
import Research.Backfill.Paper7.MomentGapD_00_00_09
import Research.Backfill.Paper7.MomentGapD_00_00_10
import Research.Backfill.Paper7.MomentGapD_00_00_11
import Research.Backfill.Paper7.MomentGapD_00_00_12
import Research.Backfill.Paper7.MomentGapD_00_00_13
import Research.Backfill.Paper7.MomentGapD_00_00_14
import Research.Backfill.Paper7.MomentGapD_00_00_15
import Research.Backfill.Paper7.MomentGapD_00_00_16
import Research.Backfill.Paper7.MomentGapD_00_00_17
import Research.Backfill.Paper7.MomentGapD_00_00_18

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

def cvalues_00_00 : Fin 19 → ℕ := ![28, 168, 204, 288, 282, 240, 492, 324, 600, 462, 300, 198, 120, 36, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_00

theorem cblock_00_00 : b4GapCBlock 0 0 = 3742 := by
  calc
    b4GapCBlock 0 0 = ∑ i : Fin 19, cvalues_00_00 i := by
      apply b4GapCBlock_of_dblocks 0 0 cvalues_00_00
      intro i
      fin_cases i
      · exact dblock_00_00_00
      · exact dblock_00_00_01
      · exact dblock_00_00_02
      · exact dblock_00_00_03
      · exact dblock_00_00_04
      · exact dblock_00_00_05
      · exact dblock_00_00_06
      · exact dblock_00_00_07
      · exact dblock_00_00_08
      · exact dblock_00_00_09
      · exact dblock_00_00_10
      · exact dblock_00_00_11
      · exact dblock_00_00_12
      · exact dblock_00_00_13
      · exact dblock_00_00_14
      · exact dblock_00_00_15
      · exact dblock_00_00_16
      · exact dblock_00_00_17
      · exact dblock_00_00_18
    _ = 3742 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_00

end Paper7MomentGapNumeric
