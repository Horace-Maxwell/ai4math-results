import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_04_00
import Research.Backfill.Paper7.MomentGapD_04_04_01
import Research.Backfill.Paper7.MomentGapD_04_04_02
import Research.Backfill.Paper7.MomentGapD_04_04_03
import Research.Backfill.Paper7.MomentGapD_04_04_04

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

def cvalues_04_04 : Fin 5 → ℕ := ![960, 480, 420, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_04

theorem cblock_04_04 : b4GapCBlock 4 4 = 1860 := by
  calc
    b4GapCBlock 4 4 = ∑ i : Fin 5, cvalues_04_04 i := by
      apply b4GapCBlock_of_dblocks 4 4 cvalues_04_04
      intro i
      fin_cases i
      · exact dblock_04_04_00
      · exact dblock_04_04_01
      · exact dblock_04_04_02
      · exact dblock_04_04_03
      · exact dblock_04_04_04
    _ = 1860 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_04

end Paper7MomentGapNumeric
