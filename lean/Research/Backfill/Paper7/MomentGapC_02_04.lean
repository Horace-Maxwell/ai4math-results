import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_04_00
import Research.Backfill.Paper7.MomentGapD_02_04_01
import Research.Backfill.Paper7.MomentGapD_02_04_02
import Research.Backfill.Paper7.MomentGapD_02_04_03
import Research.Backfill.Paper7.MomentGapD_02_04_04
import Research.Backfill.Paper7.MomentGapD_02_04_05
import Research.Backfill.Paper7.MomentGapD_02_04_06
import Research.Backfill.Paper7.MomentGapD_02_04_07
import Research.Backfill.Paper7.MomentGapD_02_04_08

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

def cvalues_02_04 : Fin 9 → ℕ := ![1212, 2640, 4536, 0, 1104, 780, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_04

theorem cblock_02_04 : b4GapCBlock 2 4 = 10272 := by
  calc
    b4GapCBlock 2 4 = ∑ i : Fin 9, cvalues_02_04 i := by
      apply b4GapCBlock_of_dblocks 2 4 cvalues_02_04
      intro i
      fin_cases i
      · exact dblock_02_04_00
      · exact dblock_02_04_01
      · exact dblock_02_04_02
      · exact dblock_02_04_03
      · exact dblock_02_04_04
      · exact dblock_02_04_05
      · exact dblock_02_04_06
      · exact dblock_02_04_07
      · exact dblock_02_04_08
    _ = 10272 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_04

end Paper7MomentGapNumeric
