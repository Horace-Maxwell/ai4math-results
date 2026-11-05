import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_01_01_00
import Research.Backfill.Paper7.MomentGapD_01_01_01
import Research.Backfill.Paper7.MomentGapD_01_01_02
import Research.Backfill.Paper7.MomentGapD_01_01_03
import Research.Backfill.Paper7.MomentGapD_01_01_04
import Research.Backfill.Paper7.MomentGapD_01_01_05
import Research.Backfill.Paper7.MomentGapD_01_01_06
import Research.Backfill.Paper7.MomentGapD_01_01_07
import Research.Backfill.Paper7.MomentGapD_01_01_08
import Research.Backfill.Paper7.MomentGapD_01_01_09
import Research.Backfill.Paper7.MomentGapD_01_01_10
import Research.Backfill.Paper7.MomentGapD_01_01_11
import Research.Backfill.Paper7.MomentGapD_01_01_12
import Research.Backfill.Paper7.MomentGapD_01_01_13
import Research.Backfill.Paper7.MomentGapD_01_01_14
import Research.Backfill.Paper7.MomentGapD_01_01_15

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

def cvalues_01_01 : Fin 16 → ℕ := ![996, 2832, 3012, 3432, 2376, 2280, 1032, 2904, 3792, 24, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_01_01

theorem cblock_01_01 : b4GapCBlock 1 1 = 22680 := by
  calc
    b4GapCBlock 1 1 = ∑ i : Fin 16, cvalues_01_01 i := by
      apply b4GapCBlock_of_dblocks 1 1 cvalues_01_01
      intro i
      fin_cases i
      · exact dblock_01_01_00
      · exact dblock_01_01_01
      · exact dblock_01_01_02
      · exact dblock_01_01_03
      · exact dblock_01_01_04
      · exact dblock_01_01_05
      · exact dblock_01_01_06
      · exact dblock_01_01_07
      · exact dblock_01_01_08
      · exact dblock_01_01_09
      · exact dblock_01_01_10
      · exact dblock_01_01_11
      · exact dblock_01_01_12
      · exact dblock_01_01_13
      · exact dblock_01_01_14
      · exact dblock_01_01_15
    _ = 22680 := by decide
#print axioms Paper7MomentGapNumeric.cblock_01_01

end Paper7MomentGapNumeric
