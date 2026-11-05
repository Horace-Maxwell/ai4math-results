import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C11

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

theorem row_00_00_11_00 : b4RowContribution (![0, 0, 11, 11] : Fin 4 → ℕ) = 9 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 11, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_11
#print axioms Paper7MomentGapNumeric.row_00_00_11_00

theorem weighted_00_00_11_00 : b4RawGapContribution ![0, 0, 11, 0] = 54 := by
  calc
    b4RawGapContribution ![0, 0, 11, 0] = b4GapPatternWeight 0 11 0 * 9 :=
      b4GapContribution_from_row 0 0 11 0 9 row_00_00_11_00
    _ = 54 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_00

theorem row_00_00_11_01 : b4RowContribution (![0, 0, 11, 12] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 11, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_12
#print axioms Paper7MomentGapNumeric.row_00_00_11_01

theorem weighted_00_00_11_01 : b4RawGapContribution ![0, 0, 11, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 1] = b4GapPatternWeight 0 11 1 * 0 :=
      b4GapContribution_from_row 0 0 11 1 0 row_00_00_11_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_01

theorem row_00_00_11_02 : b4RowContribution (![0, 0, 11, 13] : Fin 4 → ℕ) = 12 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 11, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_13
#print axioms Paper7MomentGapNumeric.row_00_00_11_02

theorem weighted_00_00_11_02 : b4RawGapContribution ![0, 0, 11, 2] = 144 := by
  calc
    b4RawGapContribution ![0, 0, 11, 2] = b4GapPatternWeight 0 11 2 * 12 :=
      b4GapContribution_from_row 0 0 11 2 12 row_00_00_11_02
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_02

theorem row_00_00_11_03 : b4RowContribution (![0, 0, 11, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 11, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_14
#print axioms Paper7MomentGapNumeric.row_00_00_11_03

theorem weighted_00_00_11_03 : b4RawGapContribution ![0, 0, 11, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 3] = b4GapPatternWeight 0 11 3 * 0 :=
      b4GapContribution_from_row 0 0 11 3 0 row_00_00_11_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_03

theorem row_00_00_11_04 : b4RowContribution (![0, 0, 11, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 11, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_15
#print axioms Paper7MomentGapNumeric.row_00_00_11_04

theorem weighted_00_00_11_04 : b4RawGapContribution ![0, 0, 11, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 4] = b4GapPatternWeight 0 11 4 * 0 :=
      b4GapContribution_from_row 0 0 11 4 0 row_00_00_11_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_04

theorem row_00_00_11_05 : b4RowContribution (![0, 0, 11, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 11, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_16
#print axioms Paper7MomentGapNumeric.row_00_00_11_05

theorem weighted_00_00_11_05 : b4RawGapContribution ![0, 0, 11, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 5] = b4GapPatternWeight 0 11 5 * 0 :=
      b4GapContribution_from_row 0 0 11 5 0 row_00_00_11_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_05

theorem row_00_00_11_06 : b4RowContribution (![0, 0, 11, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 11, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_17
#print axioms Paper7MomentGapNumeric.row_00_00_11_06

theorem weighted_00_00_11_06 : b4RawGapContribution ![0, 0, 11, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 6] = b4GapPatternWeight 0 11 6 * 0 :=
      b4GapContribution_from_row 0 0 11 6 0 row_00_00_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_06

theorem row_00_00_11_07 : b4RowContribution (![0, 0, 11, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 11, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_18
#print axioms Paper7MomentGapNumeric.row_00_00_11_07

theorem weighted_00_00_11_07 : b4RawGapContribution ![0, 0, 11, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 7] = b4GapPatternWeight 0 11 7 * 0 :=
      b4GapContribution_from_row 0 0 11 7 0 row_00_00_11_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_07

theorem row_00_00_11_08 : b4RowContribution (![0, 0, 11, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 11, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_19
#print axioms Paper7MomentGapNumeric.row_00_00_11_08

theorem weighted_00_00_11_08 : b4RawGapContribution ![0, 0, 11, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 8] = b4GapPatternWeight 0 11 8 * 0 :=
      b4GapContribution_from_row 0 0 11 8 0 row_00_00_11_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_08

theorem row_00_00_11_09 : b4RowContribution (![0, 0, 11, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 11, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_20
#print axioms Paper7MomentGapNumeric.row_00_00_11_09

theorem weighted_00_00_11_09 : b4RawGapContribution ![0, 0, 11, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 9] = b4GapPatternWeight 0 11 9 * 0 :=
      b4GapContribution_from_row 0 0 11 9 0 row_00_00_11_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_09

theorem row_00_00_11_10 : b4RowContribution (![0, 0, 11, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 11, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_21
#print axioms Paper7MomentGapNumeric.row_00_00_11_10

theorem weighted_00_00_11_10 : b4RawGapContribution ![0, 0, 11, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 10] = b4GapPatternWeight 0 11 10 * 0 :=
      b4GapContribution_from_row 0 0 11 10 0 row_00_00_11_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_10

theorem row_00_00_11_11 : b4RowContribution (![0, 0, 11, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 11, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_22
#print axioms Paper7MomentGapNumeric.row_00_00_11_11

theorem weighted_00_00_11_11 : b4RawGapContribution ![0, 0, 11, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 11] = b4GapPatternWeight 0 11 11 * 0 :=
      b4GapContribution_from_row 0 0 11 11 0 row_00_00_11_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_11

theorem row_00_00_11_12 : b4RowContribution (![0, 0, 11, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 11, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_23
#print axioms Paper7MomentGapNumeric.row_00_00_11_12

theorem weighted_00_00_11_12 : b4RawGapContribution ![0, 0, 11, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 12] = b4GapPatternWeight 0 11 12 * 0 :=
      b4GapContribution_from_row 0 0 11 12 0 row_00_00_11_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_12

theorem row_00_00_11_13 : b4RowContribution (![0, 0, 11, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 11, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_24
#print axioms Paper7MomentGapNumeric.row_00_00_11_13

theorem weighted_00_00_11_13 : b4RawGapContribution ![0, 0, 11, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 13] = b4GapPatternWeight 0 11 13 * 0 :=
      b4GapContribution_from_row 0 0 11 13 0 row_00_00_11_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_13

theorem row_00_00_11_14 : b4RowContribution (![0, 0, 11, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 11, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_25
#print axioms Paper7MomentGapNumeric.row_00_00_11_14

theorem weighted_00_00_11_14 : b4RawGapContribution ![0, 0, 11, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 14] = b4GapPatternWeight 0 11 14 * 0 :=
      b4GapContribution_from_row 0 0 11 14 0 row_00_00_11_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_14

theorem row_00_00_11_15 : b4RowContribution (![0, 0, 11, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨11, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 11, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_11_26
#print axioms Paper7MomentGapNumeric.row_00_00_11_15

theorem weighted_00_00_11_15 : b4RawGapContribution ![0, 0, 11, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 11, 15] = b4GapPatternWeight 0 11 15 * 0 :=
      b4GapContribution_from_row 0 0 11 15 0 row_00_00_11_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_11_15

def dvalues_00_00_11 : Fin 16 → ℕ := ![54, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_11

theorem dblock_00_00_11 : b4GapPatternDBlock 0 0 11 = 198 := by
  calc
    b4GapPatternDBlock 0 0 11 = ∑ d : Fin 16, dvalues_00_00_11 d := by
      apply b4GapDBlock_of_rows 0 0 11 dvalues_00_00_11
      intro d
      fin_cases d
      · exact weighted_00_00_11_00
      · exact weighted_00_00_11_01
      · exact weighted_00_00_11_02
      · exact weighted_00_00_11_03
      · exact weighted_00_00_11_04
      · exact weighted_00_00_11_05
      · exact weighted_00_00_11_06
      · exact weighted_00_00_11_07
      · exact weighted_00_00_11_08
      · exact weighted_00_00_11_09
      · exact weighted_00_00_11_10
      · exact weighted_00_00_11_11
      · exact weighted_00_00_11_12
      · exact weighted_00_00_11_13
      · exact weighted_00_00_11_14
      · exact weighted_00_00_11_15
    _ = 198 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_11

end Paper7MomentGapNumeric
