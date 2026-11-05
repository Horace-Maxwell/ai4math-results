import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_02_00
import Research.Backfill.Paper7.MomentGapD_02_02_01
import Research.Backfill.Paper7.MomentGapD_02_02_02
import Research.Backfill.Paper7.MomentGapD_02_02_03
import Research.Backfill.Paper7.MomentGapD_02_02_04
import Research.Backfill.Paper7.MomentGapD_02_02_05
import Research.Backfill.Paper7.MomentGapD_02_02_06
import Research.Backfill.Paper7.MomentGapD_02_02_07
import Research.Backfill.Paper7.MomentGapD_02_02_08
import Research.Backfill.Paper7.MomentGapD_02_02_09
import Research.Backfill.Paper7.MomentGapD_02_02_10
import Research.Backfill.Paper7.MomentGapD_02_02_11

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

def cvalues_02_02 : Fin 12 → ℕ := ![1644, 2904, 5040, 3600, 3240, 2520, 0, 1440, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_02

theorem cblock_02_02 : b4GapCBlock 2 2 = 20388 := by
  calc
    b4GapCBlock 2 2 = ∑ i : Fin 12, cvalues_02_02 i := by
      apply b4GapCBlock_of_dblocks 2 2 cvalues_02_02
      intro i
      fin_cases i
      · exact dblock_02_02_00
      · exact dblock_02_02_01
      · exact dblock_02_02_02
      · exact dblock_02_02_03
      · exact dblock_02_02_04
      · exact dblock_02_02_05
      · exact dblock_02_02_06
      · exact dblock_02_02_07
      · exact dblock_02_02_08
      · exact dblock_02_02_09
      · exact dblock_02_02_10
      · exact dblock_02_02_11
    _ = 20388 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_02

end Paper7MomentGapNumeric
