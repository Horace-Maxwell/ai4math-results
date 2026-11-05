import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_08_00_00
import Research.Backfill.Paper7.MomentGapD_08_00_01
import Research.Backfill.Paper7.MomentGapD_08_00_02

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

def cvalues_08_00 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_08_00

theorem cblock_08_00 : b4GapCBlock 8 0 = 0 := by
  calc
    b4GapCBlock 8 0 = ∑ i : Fin 3, cvalues_08_00 i := by
      apply b4GapCBlock_of_dblocks 8 0 cvalues_08_00
      intro i
      fin_cases i
      · exact dblock_08_00_00
      · exact dblock_08_00_01
      · exact dblock_08_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_08_00

end Paper7MomentGapNumeric
