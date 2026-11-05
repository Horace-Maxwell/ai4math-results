import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_07_00_00
import Research.Backfill.Paper7.MomentGapD_07_00_01
import Research.Backfill.Paper7.MomentGapD_07_00_02
import Research.Backfill.Paper7.MomentGapD_07_00_03
import Research.Backfill.Paper7.MomentGapD_07_00_04

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

def cvalues_07_00 : Fin 5 → ℕ := ![0, 48, 240, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_07_00

theorem cblock_07_00 : b4GapCBlock 7 0 = 288 := by
  calc
    b4GapCBlock 7 0 = ∑ i : Fin 5, cvalues_07_00 i := by
      apply b4GapCBlock_of_dblocks 7 0 cvalues_07_00
      intro i
      fin_cases i
      · exact dblock_07_00_00
      · exact dblock_07_00_01
      · exact dblock_07_00_02
      · exact dblock_07_00_03
      · exact dblock_07_00_04
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.cblock_07_00

end Paper7MomentGapNumeric
