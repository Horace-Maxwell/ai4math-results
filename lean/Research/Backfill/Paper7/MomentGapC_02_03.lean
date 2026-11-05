import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_03_00
import Research.Backfill.Paper7.MomentGapD_02_03_01
import Research.Backfill.Paper7.MomentGapD_02_03_02
import Research.Backfill.Paper7.MomentGapD_02_03_03
import Research.Backfill.Paper7.MomentGapD_02_03_04
import Research.Backfill.Paper7.MomentGapD_02_03_05
import Research.Backfill.Paper7.MomentGapD_02_03_06
import Research.Backfill.Paper7.MomentGapD_02_03_07
import Research.Backfill.Paper7.MomentGapD_02_03_08
import Research.Backfill.Paper7.MomentGapD_02_03_09
import Research.Backfill.Paper7.MomentGapD_02_03_10

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

def cvalues_02_03 : Fin 11 → ℕ := ![1668, 1536, 1944, 456, 1992, 2484, 972, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_03

theorem cblock_02_03 : b4GapCBlock 2 3 = 11052 := by
  calc
    b4GapCBlock 2 3 = ∑ i : Fin 11, cvalues_02_03 i := by
      apply b4GapCBlock_of_dblocks 2 3 cvalues_02_03
      intro i
      fin_cases i
      · exact dblock_02_03_00
      · exact dblock_02_03_01
      · exact dblock_02_03_02
      · exact dblock_02_03_03
      · exact dblock_02_03_04
      · exact dblock_02_03_05
      · exact dblock_02_03_06
      · exact dblock_02_03_07
      · exact dblock_02_03_08
      · exact dblock_02_03_09
      · exact dblock_02_03_10
    _ = 11052 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_03

end Paper7MomentGapNumeric
