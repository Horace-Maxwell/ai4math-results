import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_01_04_00
import Research.Backfill.Paper7.MomentGapD_01_04_01
import Research.Backfill.Paper7.MomentGapD_01_04_02
import Research.Backfill.Paper7.MomentGapD_01_04_03
import Research.Backfill.Paper7.MomentGapD_01_04_04
import Research.Backfill.Paper7.MomentGapD_01_04_05
import Research.Backfill.Paper7.MomentGapD_01_04_06
import Research.Backfill.Paper7.MomentGapD_01_04_07
import Research.Backfill.Paper7.MomentGapD_01_04_08
import Research.Backfill.Paper7.MomentGapD_01_04_09
import Research.Backfill.Paper7.MomentGapD_01_04_10

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

def cvalues_01_04 : Fin 11 → ℕ := ![1668, 3816, 4008, 2616, 3168, 3168, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_01_04

theorem cblock_01_04 : b4GapCBlock 1 4 = 18444 := by
  calc
    b4GapCBlock 1 4 = ∑ i : Fin 11, cvalues_01_04 i := by
      apply b4GapCBlock_of_dblocks 1 4 cvalues_01_04
      intro i
      fin_cases i
      · exact dblock_01_04_00
      · exact dblock_01_04_01
      · exact dblock_01_04_02
      · exact dblock_01_04_03
      · exact dblock_01_04_04
      · exact dblock_01_04_05
      · exact dblock_01_04_06
      · exact dblock_01_04_07
      · exact dblock_01_04_08
      · exact dblock_01_04_09
      · exact dblock_01_04_10
    _ = 18444 := by decide
#print axioms Paper7MomentGapNumeric.cblock_01_04

end Paper7MomentGapNumeric
