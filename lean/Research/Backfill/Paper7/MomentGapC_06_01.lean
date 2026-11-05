import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_06_01_00
import Research.Backfill.Paper7.MomentGapD_06_01_01
import Research.Backfill.Paper7.MomentGapD_06_01_02
import Research.Backfill.Paper7.MomentGapD_06_01_03
import Research.Backfill.Paper7.MomentGapD_06_01_04
import Research.Backfill.Paper7.MomentGapD_06_01_05

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

def cvalues_06_01 : Fin 6 → ℕ := ![684, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_06_01

theorem cblock_06_01 : b4GapCBlock 6 1 = 684 := by
  calc
    b4GapCBlock 6 1 = ∑ i : Fin 6, cvalues_06_01 i := by
      apply b4GapCBlock_of_dblocks 6 1 cvalues_06_01
      intro i
      fin_cases i
      · exact dblock_06_01_00
      · exact dblock_06_01_01
      · exact dblock_06_01_02
      · exact dblock_06_01_03
      · exact dblock_06_01_04
      · exact dblock_06_01_05
    _ = 684 := by decide
#print axioms Paper7MomentGapNumeric.cblock_06_01

end Paper7MomentGapNumeric
