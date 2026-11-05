import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_05_00
import Research.Backfill.Paper7.MomentGapD_04_05_01
import Research.Backfill.Paper7.MomentGapD_04_05_02
import Research.Backfill.Paper7.MomentGapD_04_05_03

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

def cvalues_04_05 : Fin 4 → ℕ := ![660, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_05

theorem cblock_04_05 : b4GapCBlock 4 5 = 660 := by
  calc
    b4GapCBlock 4 5 = ∑ i : Fin 4, cvalues_04_05 i := by
      apply b4GapCBlock_of_dblocks 4 5 cvalues_04_05
      intro i
      fin_cases i
      · exact dblock_04_05_00
      · exact dblock_04_05_01
      · exact dblock_04_05_02
      · exact dblock_04_05_03
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_05

end Paper7MomentGapNumeric
