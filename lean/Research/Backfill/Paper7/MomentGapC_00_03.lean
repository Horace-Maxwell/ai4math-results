import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_03_00
import Research.Backfill.Paper7.MomentGapD_00_03_01
import Research.Backfill.Paper7.MomentGapD_00_03_02
import Research.Backfill.Paper7.MomentGapD_00_03_03
import Research.Backfill.Paper7.MomentGapD_00_03_04
import Research.Backfill.Paper7.MomentGapD_00_03_05
import Research.Backfill.Paper7.MomentGapD_00_03_06
import Research.Backfill.Paper7.MomentGapD_00_03_07
import Research.Backfill.Paper7.MomentGapD_00_03_08
import Research.Backfill.Paper7.MomentGapD_00_03_09
import Research.Backfill.Paper7.MomentGapD_00_03_10
import Research.Backfill.Paper7.MomentGapD_00_03_11
import Research.Backfill.Paper7.MomentGapD_00_03_12
import Research.Backfill.Paper7.MomentGapD_00_03_13
import Research.Backfill.Paper7.MomentGapD_00_03_14

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

def cvalues_00_03 : Fin 15 → ℕ := ![724, 2568, 2280, 1224, 2304, 1272, 2280, 2136, 912, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_03

theorem cblock_00_03 : b4GapCBlock 0 3 = 15700 := by
  calc
    b4GapCBlock 0 3 = ∑ i : Fin 15, cvalues_00_03 i := by
      apply b4GapCBlock_of_dblocks 0 3 cvalues_00_03
      intro i
      fin_cases i
      · exact dblock_00_03_00
      · exact dblock_00_03_01
      · exact dblock_00_03_02
      · exact dblock_00_03_03
      · exact dblock_00_03_04
      · exact dblock_00_03_05
      · exact dblock_00_03_06
      · exact dblock_00_03_07
      · exact dblock_00_03_08
      · exact dblock_00_03_09
      · exact dblock_00_03_10
      · exact dblock_00_03_11
      · exact dblock_00_03_12
      · exact dblock_00_03_13
      · exact dblock_00_03_14
    _ = 15700 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_03

end Paper7MomentGapNumeric
