import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_06_03_00
import Research.Backfill.Paper7.MomentGapD_06_03_01
import Research.Backfill.Paper7.MomentGapD_06_03_02

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

def cvalues_06_03 : Fin 3 → ℕ := ![80, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_06_03

theorem cblock_06_03 : b4GapCBlock 6 3 = 80 := by
  calc
    b4GapCBlock 6 3 = ∑ i : Fin 3, cvalues_06_03 i := by
      apply b4GapCBlock_of_dblocks 6 3 cvalues_06_03
      intro i
      fin_cases i
      · exact dblock_06_03_00
      · exact dblock_06_03_01
      · exact dblock_06_03_02
    _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.cblock_06_03

end Paper7MomentGapNumeric
