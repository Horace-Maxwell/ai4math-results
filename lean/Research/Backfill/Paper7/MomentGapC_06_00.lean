import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_06_00_00
import Research.Backfill.Paper7.MomentGapD_06_00_01
import Research.Backfill.Paper7.MomentGapD_06_00_02
import Research.Backfill.Paper7.MomentGapD_06_00_03
import Research.Backfill.Paper7.MomentGapD_06_00_04
import Research.Backfill.Paper7.MomentGapD_06_00_05
import Research.Backfill.Paper7.MomentGapD_06_00_06

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

def cvalues_06_00 : Fin 7 → ℕ := ![156, 1872, 420, 6, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_06_00

theorem cblock_06_00 : b4GapCBlock 6 0 = 2454 := by
  calc
    b4GapCBlock 6 0 = ∑ i : Fin 7, cvalues_06_00 i := by
      apply b4GapCBlock_of_dblocks 6 0 cvalues_06_00
      intro i
      fin_cases i
      · exact dblock_06_00_00
      · exact dblock_06_00_01
      · exact dblock_06_00_02
      · exact dblock_06_00_03
      · exact dblock_06_00_04
      · exact dblock_06_00_05
      · exact dblock_06_00_06
    _ = 2454 := by decide
#print axioms Paper7MomentGapNumeric.cblock_06_00

end Paper7MomentGapNumeric
