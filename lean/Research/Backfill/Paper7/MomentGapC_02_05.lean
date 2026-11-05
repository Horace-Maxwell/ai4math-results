import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_05_00
import Research.Backfill.Paper7.MomentGapD_02_05_01
import Research.Backfill.Paper7.MomentGapD_02_05_02
import Research.Backfill.Paper7.MomentGapD_02_05_03
import Research.Backfill.Paper7.MomentGapD_02_05_04
import Research.Backfill.Paper7.MomentGapD_02_05_05
import Research.Backfill.Paper7.MomentGapD_02_05_06
import Research.Backfill.Paper7.MomentGapD_02_05_07

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

def cvalues_02_05 : Fin 8 → ℕ := ![2772, 840, 696, 744, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_05

theorem cblock_02_05 : b4GapCBlock 2 5 = 5052 := by
  calc
    b4GapCBlock 2 5 = ∑ i : Fin 8, cvalues_02_05 i := by
      apply b4GapCBlock_of_dblocks 2 5 cvalues_02_05
      intro i
      fin_cases i
      · exact dblock_02_05_00
      · exact dblock_02_05_01
      · exact dblock_02_05_02
      · exact dblock_02_05_03
      · exact dblock_02_05_04
      · exact dblock_02_05_05
      · exact dblock_02_05_06
      · exact dblock_02_05_07
    _ = 5052 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_05

end Paper7MomentGapNumeric
