import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_07_01_00
import Research.Backfill.Paper7.MomentGapD_07_01_01
import Research.Backfill.Paper7.MomentGapD_07_01_02
import Research.Backfill.Paper7.MomentGapD_07_01_03

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

def cvalues_07_01 : Fin 4 → ℕ := ![420, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_07_01

theorem cblock_07_01 : b4GapCBlock 7 1 = 420 := by
  calc
    b4GapCBlock 7 1 = ∑ i : Fin 4, cvalues_07_01 i := by
      apply b4GapCBlock_of_dblocks 7 1 cvalues_07_01
      intro i
      fin_cases i
      · exact dblock_07_01_00
      · exact dblock_07_01_01
      · exact dblock_07_01_02
      · exact dblock_07_01_03
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.cblock_07_01

end Paper7MomentGapNumeric
