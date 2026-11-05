import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_08_00
import Research.Backfill.Paper7.MomentGapC_08_01

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

def avalues_08 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.avalues_08

theorem ablock_08 : b4GapABlock 8 = 0 := by
  calc
    b4GapABlock 8 = ∑ i : Fin 2, avalues_08 i := by
      apply b4GapABlock_of_cblocks 8 avalues_08
      intro i
      fin_cases i
      · exact cblock_08_00
      · exact cblock_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.ablock_08

end Paper7MomentGapNumeric
