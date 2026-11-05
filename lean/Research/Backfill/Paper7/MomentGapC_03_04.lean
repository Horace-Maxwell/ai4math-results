import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_03_04_00
import Research.Backfill.Paper7.MomentGapD_03_04_01
import Research.Backfill.Paper7.MomentGapD_03_04_02
import Research.Backfill.Paper7.MomentGapD_03_04_03
import Research.Backfill.Paper7.MomentGapD_03_04_04
import Research.Backfill.Paper7.MomentGapD_03_04_05
import Research.Backfill.Paper7.MomentGapD_03_04_06

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

def cvalues_03_04 : Fin 7 → ℕ := ![1128, 3816, 816, 1800, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_03_04

theorem cblock_03_04 : b4GapCBlock 3 4 = 7560 := by
  calc
    b4GapCBlock 3 4 = ∑ i : Fin 7, cvalues_03_04 i := by
      apply b4GapCBlock_of_dblocks 3 4 cvalues_03_04
      intro i
      fin_cases i
      · exact dblock_03_04_00
      · exact dblock_03_04_01
      · exact dblock_03_04_02
      · exact dblock_03_04_03
      · exact dblock_03_04_04
      · exact dblock_03_04_05
      · exact dblock_03_04_06
    _ = 7560 := by decide
#print axioms Paper7MomentGapNumeric.cblock_03_04

end Paper7MomentGapNumeric
