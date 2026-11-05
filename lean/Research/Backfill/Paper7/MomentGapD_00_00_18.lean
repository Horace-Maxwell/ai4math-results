import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C18

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

theorem row_00_00_18_00 : b4RowContribution (![0, 0, 18, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨18, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 18, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_18_18
#print axioms Paper7MomentGapNumeric.row_00_00_18_00

theorem weighted_00_00_18_00 : b4RawGapContribution ![0, 0, 18, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 18, 0] = b4GapPatternWeight 0 18 0 * 0 :=
      b4GapContribution_from_row 0 0 18 0 0 row_00_00_18_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_18_00

theorem row_00_00_18_01 : b4RowContribution (![0, 0, 18, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨18, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 18, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_18_19
#print axioms Paper7MomentGapNumeric.row_00_00_18_01

theorem weighted_00_00_18_01 : b4RawGapContribution ![0, 0, 18, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 18, 1] = b4GapPatternWeight 0 18 1 * 0 :=
      b4GapContribution_from_row 0 0 18 1 0 row_00_00_18_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_18_01

def dvalues_00_00_18 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_18

theorem dblock_00_00_18 : b4GapPatternDBlock 0 0 18 = 0 := by
  calc
    b4GapPatternDBlock 0 0 18 = ∑ d : Fin 2, dvalues_00_00_18 d := by
      apply b4GapDBlock_of_rows 0 0 18 dvalues_00_00_18
      intro d
      fin_cases d
      · exact weighted_00_00_18_00
      · exact weighted_00_00_18_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_18

end Paper7MomentGapNumeric
