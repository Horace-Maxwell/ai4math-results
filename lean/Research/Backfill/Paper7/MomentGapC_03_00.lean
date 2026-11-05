import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_03_00_00
import Research.Backfill.Paper7.MomentGapD_03_00_01
import Research.Backfill.Paper7.MomentGapD_03_00_02
import Research.Backfill.Paper7.MomentGapD_03_00_03
import Research.Backfill.Paper7.MomentGapD_03_00_04
import Research.Backfill.Paper7.MomentGapD_03_00_05
import Research.Backfill.Paper7.MomentGapD_03_00_06
import Research.Backfill.Paper7.MomentGapD_03_00_07
import Research.Backfill.Paper7.MomentGapD_03_00_08
import Research.Backfill.Paper7.MomentGapD_03_00_09
import Research.Backfill.Paper7.MomentGapD_03_00_10
import Research.Backfill.Paper7.MomentGapD_03_00_11
import Research.Backfill.Paper7.MomentGapD_03_00_12

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

def cvalues_03_00 : Fin 13 → ℕ := ![556, 2436, 576, 1716, 576, 2064, 0, 696, 1008, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_03_00

theorem cblock_03_00 : b4GapCBlock 3 0 = 9628 := by
  calc
    b4GapCBlock 3 0 = ∑ i : Fin 13, cvalues_03_00 i := by
      apply b4GapCBlock_of_dblocks 3 0 cvalues_03_00
      intro i
      fin_cases i
      · exact dblock_03_00_00
      · exact dblock_03_00_01
      · exact dblock_03_00_02
      · exact dblock_03_00_03
      · exact dblock_03_00_04
      · exact dblock_03_00_05
      · exact dblock_03_00_06
      · exact dblock_03_00_07
      · exact dblock_03_00_08
      · exact dblock_03_00_09
      · exact dblock_03_00_10
      · exact dblock_03_00_11
      · exact dblock_03_00_12
    _ = 9628 := by decide
#print axioms Paper7MomentGapNumeric.cblock_03_00

end Paper7MomentGapNumeric
