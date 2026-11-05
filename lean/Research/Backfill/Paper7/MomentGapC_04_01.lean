import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_01_00
import Research.Backfill.Paper7.MomentGapD_04_01_01
import Research.Backfill.Paper7.MomentGapD_04_01_02
import Research.Backfill.Paper7.MomentGapD_04_01_03
import Research.Backfill.Paper7.MomentGapD_04_01_04
import Research.Backfill.Paper7.MomentGapD_04_01_05
import Research.Backfill.Paper7.MomentGapD_04_01_06
import Research.Backfill.Paper7.MomentGapD_04_01_07
import Research.Backfill.Paper7.MomentGapD_04_01_08
import Research.Backfill.Paper7.MomentGapD_04_01_09

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

def cvalues_04_01 : Fin 10 → ℕ := ![420, 1896, 1320, 3384, 3960, 480, 420, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_01

theorem cblock_04_01 : b4GapCBlock 4 1 = 11880 := by
  calc
    b4GapCBlock 4 1 = ∑ i : Fin 10, cvalues_04_01 i := by
      apply b4GapCBlock_of_dblocks 4 1 cvalues_04_01
      intro i
      fin_cases i
      · exact dblock_04_01_00
      · exact dblock_04_01_01
      · exact dblock_04_01_02
      · exact dblock_04_01_03
      · exact dblock_04_01_04
      · exact dblock_04_01_05
      · exact dblock_04_01_06
      · exact dblock_04_01_07
      · exact dblock_04_01_08
      · exact dblock_04_01_09
    _ = 11880 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_01

end Paper7MomentGapNumeric
