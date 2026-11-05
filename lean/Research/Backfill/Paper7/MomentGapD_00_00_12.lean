import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C12

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

theorem row_00_00_12_00 : b4RowContribution (![0, 0, 12, 12] : Fin 4 → ℕ) = 20 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 12, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_12
#print axioms Paper7MomentGapNumeric.row_00_00_12_00

theorem weighted_00_00_12_00 : b4RawGapContribution ![0, 0, 12, 0] = 120 := by
  calc
    b4RawGapContribution ![0, 0, 12, 0] = b4GapPatternWeight 0 12 0 * 20 :=
      b4GapContribution_from_row 0 0 12 0 20 row_00_00_12_00
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_00

theorem row_00_00_12_01 : b4RowContribution (![0, 0, 12, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 12, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_13
#print axioms Paper7MomentGapNumeric.row_00_00_12_01

theorem weighted_00_00_12_01 : b4RawGapContribution ![0, 0, 12, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 1] = b4GapPatternWeight 0 12 1 * 0 :=
      b4GapContribution_from_row 0 0 12 1 0 row_00_00_12_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_01

theorem row_00_00_12_02 : b4RowContribution (![0, 0, 12, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 12, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_14
#print axioms Paper7MomentGapNumeric.row_00_00_12_02

theorem weighted_00_00_12_02 : b4RawGapContribution ![0, 0, 12, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 2] = b4GapPatternWeight 0 12 2 * 0 :=
      b4GapContribution_from_row 0 0 12 2 0 row_00_00_12_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_02

theorem row_00_00_12_03 : b4RowContribution (![0, 0, 12, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 12, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_15
#print axioms Paper7MomentGapNumeric.row_00_00_12_03

theorem weighted_00_00_12_03 : b4RawGapContribution ![0, 0, 12, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 3] = b4GapPatternWeight 0 12 3 * 0 :=
      b4GapContribution_from_row 0 0 12 3 0 row_00_00_12_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_03

theorem row_00_00_12_04 : b4RowContribution (![0, 0, 12, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 12, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_16
#print axioms Paper7MomentGapNumeric.row_00_00_12_04

theorem weighted_00_00_12_04 : b4RawGapContribution ![0, 0, 12, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 4] = b4GapPatternWeight 0 12 4 * 0 :=
      b4GapContribution_from_row 0 0 12 4 0 row_00_00_12_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_04

theorem row_00_00_12_05 : b4RowContribution (![0, 0, 12, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 12, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_17
#print axioms Paper7MomentGapNumeric.row_00_00_12_05

theorem weighted_00_00_12_05 : b4RawGapContribution ![0, 0, 12, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 5] = b4GapPatternWeight 0 12 5 * 0 :=
      b4GapContribution_from_row 0 0 12 5 0 row_00_00_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_05

theorem row_00_00_12_06 : b4RowContribution (![0, 0, 12, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 12, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_18
#print axioms Paper7MomentGapNumeric.row_00_00_12_06

theorem weighted_00_00_12_06 : b4RawGapContribution ![0, 0, 12, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 6] = b4GapPatternWeight 0 12 6 * 0 :=
      b4GapContribution_from_row 0 0 12 6 0 row_00_00_12_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_06

theorem row_00_00_12_07 : b4RowContribution (![0, 0, 12, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 12, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_19
#print axioms Paper7MomentGapNumeric.row_00_00_12_07

theorem weighted_00_00_12_07 : b4RawGapContribution ![0, 0, 12, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 7] = b4GapPatternWeight 0 12 7 * 0 :=
      b4GapContribution_from_row 0 0 12 7 0 row_00_00_12_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_07

theorem row_00_00_12_08 : b4RowContribution (![0, 0, 12, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 12, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_20
#print axioms Paper7MomentGapNumeric.row_00_00_12_08

theorem weighted_00_00_12_08 : b4RawGapContribution ![0, 0, 12, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 8] = b4GapPatternWeight 0 12 8 * 0 :=
      b4GapContribution_from_row 0 0 12 8 0 row_00_00_12_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_08

theorem row_00_00_12_09 : b4RowContribution (![0, 0, 12, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 12, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_21
#print axioms Paper7MomentGapNumeric.row_00_00_12_09

theorem weighted_00_00_12_09 : b4RawGapContribution ![0, 0, 12, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 9] = b4GapPatternWeight 0 12 9 * 0 :=
      b4GapContribution_from_row 0 0 12 9 0 row_00_00_12_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_09

theorem row_00_00_12_10 : b4RowContribution (![0, 0, 12, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 12, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_22
#print axioms Paper7MomentGapNumeric.row_00_00_12_10

theorem weighted_00_00_12_10 : b4RawGapContribution ![0, 0, 12, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 10] = b4GapPatternWeight 0 12 10 * 0 :=
      b4GapContribution_from_row 0 0 12 10 0 row_00_00_12_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_10

theorem row_00_00_12_11 : b4RowContribution (![0, 0, 12, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 12, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_23
#print axioms Paper7MomentGapNumeric.row_00_00_12_11

theorem weighted_00_00_12_11 : b4RawGapContribution ![0, 0, 12, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 11] = b4GapPatternWeight 0 12 11 * 0 :=
      b4GapContribution_from_row 0 0 12 11 0 row_00_00_12_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_11

theorem row_00_00_12_12 : b4RowContribution (![0, 0, 12, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 12, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_24
#print axioms Paper7MomentGapNumeric.row_00_00_12_12

theorem weighted_00_00_12_12 : b4RawGapContribution ![0, 0, 12, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 12] = b4GapPatternWeight 0 12 12 * 0 :=
      b4GapContribution_from_row 0 0 12 12 0 row_00_00_12_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_12

theorem row_00_00_12_13 : b4RowContribution (![0, 0, 12, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨12, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 12, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_12_25
#print axioms Paper7MomentGapNumeric.row_00_00_12_13

theorem weighted_00_00_12_13 : b4RawGapContribution ![0, 0, 12, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 12, 13] = b4GapPatternWeight 0 12 13 * 0 :=
      b4GapContribution_from_row 0 0 12 13 0 row_00_00_12_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_12_13

def dvalues_00_00_12 : Fin 14 → ℕ := ![120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_12

theorem dblock_00_00_12 : b4GapPatternDBlock 0 0 12 = 120 := by
  calc
    b4GapPatternDBlock 0 0 12 = ∑ d : Fin 14, dvalues_00_00_12 d := by
      apply b4GapDBlock_of_rows 0 0 12 dvalues_00_00_12
      intro d
      fin_cases d
      · exact weighted_00_00_12_00
      · exact weighted_00_00_12_01
      · exact weighted_00_00_12_02
      · exact weighted_00_00_12_03
      · exact weighted_00_00_12_04
      · exact weighted_00_00_12_05
      · exact weighted_00_00_12_06
      · exact weighted_00_00_12_07
      · exact weighted_00_00_12_08
      · exact weighted_00_00_12_09
      · exact weighted_00_00_12_10
      · exact weighted_00_00_12_11
      · exact weighted_00_00_12_12
      · exact weighted_00_00_12_13
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_12

end Paper7MomentGapNumeric
