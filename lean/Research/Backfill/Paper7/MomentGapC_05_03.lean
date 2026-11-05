import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_05_03_00
import Research.Backfill.Paper7.MomentGapD_05_03_01
import Research.Backfill.Paper7.MomentGapD_05_03_02
import Research.Backfill.Paper7.MomentGapD_05_03_03
import Research.Backfill.Paper7.MomentGapD_05_03_04

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

def cvalues_05_03 : Fin 5 → ℕ := ![12, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_05_03

theorem cblock_05_03 : b4GapCBlock 5 3 = 12 := by
  calc
    b4GapCBlock 5 3 = ∑ i : Fin 5, cvalues_05_03 i := by
      apply b4GapCBlock_of_dblocks 5 3 cvalues_05_03
      intro i
      fin_cases i
      · exact dblock_05_03_00
      · exact dblock_05_03_01
      · exact dblock_05_03_02
      · exact dblock_05_03_03
      · exact dblock_05_03_04
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.cblock_05_03

end Paper7MomentGapNumeric
