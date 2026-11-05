import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_02_00
import Research.Backfill.Paper7.MomentGapD_00_02_01
import Research.Backfill.Paper7.MomentGapD_00_02_02
import Research.Backfill.Paper7.MomentGapD_00_02_03
import Research.Backfill.Paper7.MomentGapD_00_02_04
import Research.Backfill.Paper7.MomentGapD_00_02_05
import Research.Backfill.Paper7.MomentGapD_00_02_06
import Research.Backfill.Paper7.MomentGapD_00_02_07
import Research.Backfill.Paper7.MomentGapD_00_02_08
import Research.Backfill.Paper7.MomentGapD_00_02_09
import Research.Backfill.Paper7.MomentGapD_00_02_10
import Research.Backfill.Paper7.MomentGapD_00_02_11
import Research.Backfill.Paper7.MomentGapD_00_02_12
import Research.Backfill.Paper7.MomentGapD_00_02_13
import Research.Backfill.Paper7.MomentGapD_00_02_14
import Research.Backfill.Paper7.MomentGapD_00_02_15

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

def cvalues_00_02 : Fin 16 → ℕ := ![600, 1296, 1620, 2520, 2136, 1728, 1440, 2172, 1440, 144, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_02

theorem cblock_00_02 : b4GapCBlock 0 2 = 15096 := by
  calc
    b4GapCBlock 0 2 = ∑ i : Fin 16, cvalues_00_02 i := by
      apply b4GapCBlock_of_dblocks 0 2 cvalues_00_02
      intro i
      fin_cases i
      · exact dblock_00_02_00
      · exact dblock_00_02_01
      · exact dblock_00_02_02
      · exact dblock_00_02_03
      · exact dblock_00_02_04
      · exact dblock_00_02_05
      · exact dblock_00_02_06
      · exact dblock_00_02_07
      · exact dblock_00_02_08
      · exact dblock_00_02_09
      · exact dblock_00_02_10
      · exact dblock_00_02_11
      · exact dblock_00_02_12
      · exact dblock_00_02_13
      · exact dblock_00_02_14
      · exact dblock_00_02_15
    _ = 15096 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_02

end Paper7MomentGapNumeric
