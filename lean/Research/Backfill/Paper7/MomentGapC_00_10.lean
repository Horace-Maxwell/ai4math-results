import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_10_00
import Research.Backfill.Paper7.MomentGapD_00_10_01
import Research.Backfill.Paper7.MomentGapD_00_10_02
import Research.Backfill.Paper7.MomentGapD_00_10_03

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

def cvalues_00_10 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_10

theorem cblock_00_10 : b4GapCBlock 0 10 = 0 := by
  calc
    b4GapCBlock 0 10 = ∑ i : Fin 4, cvalues_00_10 i := by
      apply b4GapCBlock_of_dblocks 0 10 cvalues_00_10
      intro i
      fin_cases i
      · exact dblock_00_10_00
      · exact dblock_00_10_01
      · exact dblock_00_10_02
      · exact dblock_00_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_10

end Paper7MomentGapNumeric
