import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_05_00_00
import Research.Backfill.Paper7.MomentGapD_05_00_01
import Research.Backfill.Paper7.MomentGapD_05_00_02
import Research.Backfill.Paper7.MomentGapD_05_00_03
import Research.Backfill.Paper7.MomentGapD_05_00_04
import Research.Backfill.Paper7.MomentGapD_05_00_05
import Research.Backfill.Paper7.MomentGapD_05_00_06
import Research.Backfill.Paper7.MomentGapD_05_00_07
import Research.Backfill.Paper7.MomentGapD_05_00_08

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

def cvalues_05_00 : Fin 9 → ℕ := ![432, 1668, 1344, 468, 240, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_05_00

theorem cblock_05_00 : b4GapCBlock 5 0 = 4152 := by
  calc
    b4GapCBlock 5 0 = ∑ i : Fin 9, cvalues_05_00 i := by
      apply b4GapCBlock_of_dblocks 5 0 cvalues_05_00
      intro i
      fin_cases i
      · exact dblock_05_00_00
      · exact dblock_05_00_01
      · exact dblock_05_00_02
      · exact dblock_05_00_03
      · exact dblock_05_00_04
      · exact dblock_05_00_05
      · exact dblock_05_00_06
      · exact dblock_05_00_07
      · exact dblock_05_00_08
    _ = 4152 := by decide
#print axioms Paper7MomentGapNumeric.cblock_05_00

end Paper7MomentGapNumeric
