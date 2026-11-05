import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_06_02_00
import Research.Backfill.Paper7.MomentGapD_06_02_01
import Research.Backfill.Paper7.MomentGapD_06_02_02
import Research.Backfill.Paper7.MomentGapD_06_02_03

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

def cvalues_06_02 : Fin 4 → ℕ := ![0, 240, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_06_02

theorem cblock_06_02 : b4GapCBlock 6 2 = 240 := by
  calc
    b4GapCBlock 6 2 = ∑ i : Fin 4, cvalues_06_02 i := by
      apply b4GapCBlock_of_dblocks 6 2 cvalues_06_02
      intro i
      fin_cases i
      · exact dblock_06_02_00
      · exact dblock_06_02_01
      · exact dblock_06_02_02
      · exact dblock_06_02_03
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.cblock_06_02

end Paper7MomentGapNumeric
