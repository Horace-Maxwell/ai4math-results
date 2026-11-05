import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_06_00
import Research.Backfill.Paper7.MomentGapD_00_06_01
import Research.Backfill.Paper7.MomentGapD_00_06_02
import Research.Backfill.Paper7.MomentGapD_00_06_03
import Research.Backfill.Paper7.MomentGapD_00_06_04
import Research.Backfill.Paper7.MomentGapD_00_06_05
import Research.Backfill.Paper7.MomentGapD_00_06_06
import Research.Backfill.Paper7.MomentGapD_00_06_07
import Research.Backfill.Paper7.MomentGapD_00_06_08
import Research.Backfill.Paper7.MomentGapD_00_06_09

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

def cvalues_00_06 : Fin 10 → ℕ := ![768, 2064, 1008, 2520, 612, 252, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_06

theorem cblock_00_06 : b4GapCBlock 0 6 = 7224 := by
  calc
    b4GapCBlock 0 6 = ∑ i : Fin 10, cvalues_00_06 i := by
      apply b4GapCBlock_of_dblocks 0 6 cvalues_00_06
      intro i
      fin_cases i
      · exact dblock_00_06_00
      · exact dblock_00_06_01
      · exact dblock_00_06_02
      · exact dblock_00_06_03
      · exact dblock_00_06_04
      · exact dblock_00_06_05
      · exact dblock_00_06_06
      · exact dblock_00_06_07
      · exact dblock_00_06_08
      · exact dblock_00_06_09
    _ = 7224 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_06

end Paper7MomentGapNumeric
