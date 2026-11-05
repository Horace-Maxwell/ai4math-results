import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_05_01_00
import Research.Backfill.Paper7.MomentGapD_05_01_01
import Research.Backfill.Paper7.MomentGapD_05_01_02
import Research.Backfill.Paper7.MomentGapD_05_01_03
import Research.Backfill.Paper7.MomentGapD_05_01_04
import Research.Backfill.Paper7.MomentGapD_05_01_05
import Research.Backfill.Paper7.MomentGapD_05_01_06
import Research.Backfill.Paper7.MomentGapD_05_01_07

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

def cvalues_05_01 : Fin 8 → ℕ := ![0, 2496, 1992, 1380, 480, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_05_01

theorem cblock_05_01 : b4GapCBlock 5 1 = 6348 := by
  calc
    b4GapCBlock 5 1 = ∑ i : Fin 8, cvalues_05_01 i := by
      apply b4GapCBlock_of_dblocks 5 1 cvalues_05_01
      intro i
      fin_cases i
      · exact dblock_05_01_00
      · exact dblock_05_01_01
      · exact dblock_05_01_02
      · exact dblock_05_01_03
      · exact dblock_05_01_04
      · exact dblock_05_01_05
      · exact dblock_05_01_06
      · exact dblock_05_01_07
    _ = 6348 := by decide
#print axioms Paper7MomentGapNumeric.cblock_05_01

end Paper7MomentGapNumeric
