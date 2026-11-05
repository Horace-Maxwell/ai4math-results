import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_06_00
import Research.Backfill.Paper7.MomentGapD_02_06_01
import Research.Backfill.Paper7.MomentGapD_02_06_02
import Research.Backfill.Paper7.MomentGapD_02_06_03
import Research.Backfill.Paper7.MomentGapD_02_06_04
import Research.Backfill.Paper7.MomentGapD_02_06_05

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

def cvalues_02_06 : Fin 6 → ℕ := ![600, 2088, 1020, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_06

theorem cblock_02_06 : b4GapCBlock 2 6 = 3708 := by
  calc
    b4GapCBlock 2 6 = ∑ i : Fin 6, cvalues_02_06 i := by
      apply b4GapCBlock_of_dblocks 2 6 cvalues_02_06
      intro i
      fin_cases i
      · exact dblock_02_06_00
      · exact dblock_02_06_01
      · exact dblock_02_06_02
      · exact dblock_02_06_03
      · exact dblock_02_06_04
      · exact dblock_02_06_05
    _ = 3708 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_06

end Paper7MomentGapNumeric
