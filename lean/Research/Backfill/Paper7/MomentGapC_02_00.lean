import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_00_00
import Research.Backfill.Paper7.MomentGapD_02_00_01
import Research.Backfill.Paper7.MomentGapD_02_00_02
import Research.Backfill.Paper7.MomentGapD_02_00_03
import Research.Backfill.Paper7.MomentGapD_02_00_04
import Research.Backfill.Paper7.MomentGapD_02_00_05
import Research.Backfill.Paper7.MomentGapD_02_00_06
import Research.Backfill.Paper7.MomentGapD_02_00_07
import Research.Backfill.Paper7.MomentGapD_02_00_08
import Research.Backfill.Paper7.MomentGapD_02_00_09
import Research.Backfill.Paper7.MomentGapD_02_00_10
import Research.Backfill.Paper7.MomentGapD_02_00_11
import Research.Backfill.Paper7.MomentGapD_02_00_12
import Research.Backfill.Paper7.MomentGapD_02_00_13
import Research.Backfill.Paper7.MomentGapD_02_00_14

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

def cvalues_02_00 : Fin 15 → ℕ := ![512, 1536, 1782, 1896, 540, 2052, 1296, 1956, 1944, 864, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_00

theorem cblock_02_00 : b4GapCBlock 2 0 = 14378 := by
  calc
    b4GapCBlock 2 0 = ∑ i : Fin 15, cvalues_02_00 i := by
      apply b4GapCBlock_of_dblocks 2 0 cvalues_02_00
      intro i
      fin_cases i
      · exact dblock_02_00_00
      · exact dblock_02_00_01
      · exact dblock_02_00_02
      · exact dblock_02_00_03
      · exact dblock_02_00_04
      · exact dblock_02_00_05
      · exact dblock_02_00_06
      · exact dblock_02_00_07
      · exact dblock_02_00_08
      · exact dblock_02_00_09
      · exact dblock_02_00_10
      · exact dblock_02_00_11
      · exact dblock_02_00_12
      · exact dblock_02_00_13
      · exact dblock_02_00_14
    _ = 14378 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_00

end Paper7MomentGapNumeric
