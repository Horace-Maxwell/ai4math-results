import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_03_07_00
import Research.Backfill.Paper7.MomentGapD_03_07_01
import Research.Backfill.Paper7.MomentGapD_03_07_02

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

def cvalues_03_07 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_03_07

theorem cblock_03_07 : b4GapCBlock 3 7 = 0 := by
  calc
    b4GapCBlock 3 7 = ∑ i : Fin 3, cvalues_03_07 i := by
      apply b4GapCBlock_of_dblocks 3 7 cvalues_03_07
      intro i
      fin_cases i
      · exact dblock_03_07_00
      · exact dblock_03_07_01
      · exact dblock_03_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_03_07

end Paper7MomentGapNumeric
