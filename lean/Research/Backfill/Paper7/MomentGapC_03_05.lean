import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_03_05_00
import Research.Backfill.Paper7.MomentGapD_03_05_01
import Research.Backfill.Paper7.MomentGapD_03_05_02
import Research.Backfill.Paper7.MomentGapD_03_05_03
import Research.Backfill.Paper7.MomentGapD_03_05_04
import Research.Backfill.Paper7.MomentGapD_03_05_05

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

def cvalues_03_05 : Fin 6 → ℕ := ![636, 48, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_03_05

theorem cblock_03_05 : b4GapCBlock 3 5 = 684 := by
  calc
    b4GapCBlock 3 5 = ∑ i : Fin 6, cvalues_03_05 i := by
      apply b4GapCBlock_of_dblocks 3 5 cvalues_03_05
      intro i
      fin_cases i
      · exact dblock_03_05_00
      · exact dblock_03_05_01
      · exact dblock_03_05_02
      · exact dblock_03_05_03
      · exact dblock_03_05_04
      · exact dblock_03_05_05
    _ = 684 := by decide
#print axioms Paper7MomentGapNumeric.cblock_03_05

end Paper7MomentGapNumeric
