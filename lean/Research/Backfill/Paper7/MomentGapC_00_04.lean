import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_04_00
import Research.Backfill.Paper7.MomentGapD_00_04_01
import Research.Backfill.Paper7.MomentGapD_00_04_02
import Research.Backfill.Paper7.MomentGapD_00_04_03
import Research.Backfill.Paper7.MomentGapD_00_04_04
import Research.Backfill.Paper7.MomentGapD_00_04_05
import Research.Backfill.Paper7.MomentGapD_00_04_06
import Research.Backfill.Paper7.MomentGapD_00_04_07
import Research.Backfill.Paper7.MomentGapD_00_04_08
import Research.Backfill.Paper7.MomentGapD_00_04_09
import Research.Backfill.Paper7.MomentGapD_00_04_10
import Research.Backfill.Paper7.MomentGapD_00_04_11
import Research.Backfill.Paper7.MomentGapD_00_04_12

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

def cvalues_00_04 : Fin 13 → ℕ := ![1452, 1680, 1680, 1968, 2016, 1488, 2412, 480, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_04

theorem cblock_00_04 : b4GapCBlock 0 4 = 13176 := by
  calc
    b4GapCBlock 0 4 = ∑ i : Fin 13, cvalues_00_04 i := by
      apply b4GapCBlock_of_dblocks 0 4 cvalues_00_04
      intro i
      fin_cases i
      · exact dblock_00_04_00
      · exact dblock_00_04_01
      · exact dblock_00_04_02
      · exact dblock_00_04_03
      · exact dblock_00_04_04
      · exact dblock_00_04_05
      · exact dblock_00_04_06
      · exact dblock_00_04_07
      · exact dblock_00_04_08
      · exact dblock_00_04_09
      · exact dblock_00_04_10
      · exact dblock_00_04_11
      · exact dblock_00_04_12
    _ = 13176 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_04

end Paper7MomentGapNumeric
