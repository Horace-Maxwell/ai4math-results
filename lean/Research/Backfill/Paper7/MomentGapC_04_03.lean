import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_03_00
import Research.Backfill.Paper7.MomentGapD_04_03_01
import Research.Backfill.Paper7.MomentGapD_04_03_02
import Research.Backfill.Paper7.MomentGapD_04_03_03
import Research.Backfill.Paper7.MomentGapD_04_03_04
import Research.Backfill.Paper7.MomentGapD_04_03_05
import Research.Backfill.Paper7.MomentGapD_04_03_06

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

def cvalues_04_03 : Fin 7 → ℕ := ![468, 840, 660, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_03

theorem cblock_04_03 : b4GapCBlock 4 3 = 1968 := by
  calc
    b4GapCBlock 4 3 = ∑ i : Fin 7, cvalues_04_03 i := by
      apply b4GapCBlock_of_dblocks 4 3 cvalues_04_03
      intro i
      fin_cases i
      · exact dblock_04_03_00
      · exact dblock_04_03_01
      · exact dblock_04_03_02
      · exact dblock_04_03_03
      · exact dblock_04_03_04
      · exact dblock_04_03_05
      · exact dblock_04_03_06
    _ = 1968 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_03

end Paper7MomentGapNumeric
