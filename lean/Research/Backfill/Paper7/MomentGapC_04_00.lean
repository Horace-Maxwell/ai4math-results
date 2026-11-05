import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_00_00
import Research.Backfill.Paper7.MomentGapD_04_00_01
import Research.Backfill.Paper7.MomentGapD_04_00_02
import Research.Backfill.Paper7.MomentGapD_04_00_03
import Research.Backfill.Paper7.MomentGapD_04_00_04
import Research.Backfill.Paper7.MomentGapD_04_00_05
import Research.Backfill.Paper7.MomentGapD_04_00_06
import Research.Backfill.Paper7.MomentGapD_04_00_07
import Research.Backfill.Paper7.MomentGapD_04_00_08
import Research.Backfill.Paper7.MomentGapD_04_00_09
import Research.Backfill.Paper7.MomentGapD_04_00_10

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

def cvalues_04_00 : Fin 11 → ℕ := ![944, 3480, 240, 2172, 0, 1164, 450, 210, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_00

theorem cblock_04_00 : b4GapCBlock 4 0 = 8660 := by
  calc
    b4GapCBlock 4 0 = ∑ i : Fin 11, cvalues_04_00 i := by
      apply b4GapCBlock_of_dblocks 4 0 cvalues_04_00
      intro i
      fin_cases i
      · exact dblock_04_00_00
      · exact dblock_04_00_01
      · exact dblock_04_00_02
      · exact dblock_04_00_03
      · exact dblock_04_00_04
      · exact dblock_04_00_05
      · exact dblock_04_00_06
      · exact dblock_04_00_07
      · exact dblock_04_00_08
      · exact dblock_04_00_09
      · exact dblock_04_00_10
    _ = 8660 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_00

end Paper7MomentGapNumeric
