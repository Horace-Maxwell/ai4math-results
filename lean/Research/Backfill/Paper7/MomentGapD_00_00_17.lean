import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C17

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

theorem row_00_00_17_00 : b4RowContribution (![0, 0, 17, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨17, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 17, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_17_17
#print axioms Paper7MomentGapNumeric.row_00_00_17_00

theorem weighted_00_00_17_00 : b4RawGapContribution ![0, 0, 17, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 17, 0] = b4GapPatternWeight 0 17 0 * 0 :=
      b4GapContribution_from_row 0 0 17 0 0 row_00_00_17_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_17_00

theorem row_00_00_17_01 : b4RowContribution (![0, 0, 17, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨17, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 17, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_17_18
#print axioms Paper7MomentGapNumeric.row_00_00_17_01

theorem weighted_00_00_17_01 : b4RawGapContribution ![0, 0, 17, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 17, 1] = b4GapPatternWeight 0 17 1 * 0 :=
      b4GapContribution_from_row 0 0 17 1 0 row_00_00_17_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_17_01

theorem row_00_00_17_02 : b4RowContribution (![0, 0, 17, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨17, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 17, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_17_19
#print axioms Paper7MomentGapNumeric.row_00_00_17_02

theorem weighted_00_00_17_02 : b4RawGapContribution ![0, 0, 17, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 17, 2] = b4GapPatternWeight 0 17 2 * 0 :=
      b4GapContribution_from_row 0 0 17 2 0 row_00_00_17_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_17_02

theorem row_00_00_17_03 : b4RowContribution (![0, 0, 17, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨17, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 17, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_17_20
#print axioms Paper7MomentGapNumeric.row_00_00_17_03

theorem weighted_00_00_17_03 : b4RawGapContribution ![0, 0, 17, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 17, 3] = b4GapPatternWeight 0 17 3 * 0 :=
      b4GapContribution_from_row 0 0 17 3 0 row_00_00_17_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_17_03

def dvalues_00_00_17 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_17

theorem dblock_00_00_17 : b4GapPatternDBlock 0 0 17 = 0 := by
  calc
    b4GapPatternDBlock 0 0 17 = ∑ d : Fin 4, dvalues_00_00_17 d := by
      apply b4GapDBlock_of_rows 0 0 17 dvalues_00_00_17
      intro d
      fin_cases d
      · exact weighted_00_00_17_00
      · exact weighted_00_00_17_01
      · exact weighted_00_00_17_02
      · exact weighted_00_00_17_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_17

end Paper7MomentGapNumeric
