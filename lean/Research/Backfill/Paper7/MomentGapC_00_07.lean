import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_07_00
import Research.Backfill.Paper7.MomentGapD_00_07_01
import Research.Backfill.Paper7.MomentGapD_00_07_02
import Research.Backfill.Paper7.MomentGapD_00_07_03
import Research.Backfill.Paper7.MomentGapD_00_07_04
import Research.Backfill.Paper7.MomentGapD_00_07_05
import Research.Backfill.Paper7.MomentGapD_00_07_06
import Research.Backfill.Paper7.MomentGapD_00_07_07
import Research.Backfill.Paper7.MomentGapD_00_07_08

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

def cvalues_00_07 : Fin 9 → ℕ := ![588, 3672, 1920, 1248, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_07

theorem cblock_00_07 : b4GapCBlock 0 7 = 7428 := by
  calc
    b4GapCBlock 0 7 = ∑ i : Fin 9, cvalues_00_07 i := by
      apply b4GapCBlock_of_dblocks 0 7 cvalues_00_07
      intro i
      fin_cases i
      · exact dblock_00_07_00
      · exact dblock_00_07_01
      · exact dblock_00_07_02
      · exact dblock_00_07_03
      · exact dblock_00_07_04
      · exact dblock_00_07_05
      · exact dblock_00_07_06
      · exact dblock_00_07_07
      · exact dblock_00_07_08
    _ = 7428 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_07

end Paper7MomentGapNumeric
