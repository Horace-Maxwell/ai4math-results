import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_09_00
import Research.Backfill.Paper7.MomentGapD_00_09_01
import Research.Backfill.Paper7.MomentGapD_00_09_02
import Research.Backfill.Paper7.MomentGapD_00_09_03
import Research.Backfill.Paper7.MomentGapD_00_09_04
import Research.Backfill.Paper7.MomentGapD_00_09_05

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

def cvalues_00_09 : Fin 6 → ℕ := ![468, 612, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_09

theorem cblock_00_09 : b4GapCBlock 0 9 = 1080 := by
  calc
    b4GapCBlock 0 9 = ∑ i : Fin 6, cvalues_00_09 i := by
      apply b4GapCBlock_of_dblocks 0 9 cvalues_00_09
      intro i
      fin_cases i
      · exact dblock_00_09_00
      · exact dblock_00_09_01
      · exact dblock_00_09_02
      · exact dblock_00_09_03
      · exact dblock_00_09_04
      · exact dblock_00_09_05
    _ = 1080 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_09

end Paper7MomentGapNumeric
