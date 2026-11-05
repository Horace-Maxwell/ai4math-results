import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_07_00
import Research.Backfill.Paper7.MomentGapD_02_07_01
import Research.Backfill.Paper7.MomentGapD_02_07_02
import Research.Backfill.Paper7.MomentGapD_02_07_03
import Research.Backfill.Paper7.MomentGapD_02_07_04

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

def cvalues_02_07 : Fin 5 → ℕ := ![0, 228, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_07

theorem cblock_02_07 : b4GapCBlock 2 7 = 228 := by
  calc
    b4GapCBlock 2 7 = ∑ i : Fin 5, cvalues_02_07 i := by
      apply b4GapCBlock_of_dblocks 2 7 cvalues_02_07
      intro i
      fin_cases i
      · exact dblock_02_07_00
      · exact dblock_02_07_01
      · exact dblock_02_07_02
      · exact dblock_02_07_03
      · exact dblock_02_07_04
    _ = 228 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_07

end Paper7MomentGapNumeric
