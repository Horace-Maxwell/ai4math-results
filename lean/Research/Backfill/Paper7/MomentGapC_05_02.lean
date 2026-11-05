import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_05_02_00
import Research.Backfill.Paper7.MomentGapD_05_02_01
import Research.Backfill.Paper7.MomentGapD_05_02_02
import Research.Backfill.Paper7.MomentGapD_05_02_03
import Research.Backfill.Paper7.MomentGapD_05_02_04
import Research.Backfill.Paper7.MomentGapD_05_02_05

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

def cvalues_05_02 : Fin 6 → ℕ := ![1392, 480, 24, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_05_02

theorem cblock_05_02 : b4GapCBlock 5 2 = 1896 := by
  calc
    b4GapCBlock 5 2 = ∑ i : Fin 6, cvalues_05_02 i := by
      apply b4GapCBlock_of_dblocks 5 2 cvalues_05_02
      intro i
      fin_cases i
      · exact dblock_05_02_00
      · exact dblock_05_02_01
      · exact dblock_05_02_02
      · exact dblock_05_02_03
      · exact dblock_05_02_04
      · exact dblock_05_02_05
    _ = 1896 := by decide
#print axioms Paper7MomentGapNumeric.cblock_05_02

end Paper7MomentGapNumeric
