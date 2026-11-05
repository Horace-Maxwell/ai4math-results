import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C05

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

theorem row_00_00_05_00 : b4RowContribution (![0, 0, 5, 5] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 5, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_05
#print axioms Paper7MomentGapNumeric.row_00_00_05_00

theorem weighted_00_00_05_00 : b4RawGapContribution ![0, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 0 0 5 0 0 row_00_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_00

theorem row_00_00_05_01 : b4RowContribution (![0, 0, 5, 6] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 5, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_06
#print axioms Paper7MomentGapNumeric.row_00_00_05_01

theorem weighted_00_00_05_01 : b4RawGapContribution ![0, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 0 0 5 1 0 row_00_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_01

theorem row_00_00_05_02 : b4RowContribution (![0, 0, 5, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 5, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_07
#print axioms Paper7MomentGapNumeric.row_00_00_05_02

theorem weighted_00_00_05_02 : b4RawGapContribution ![0, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 0 0 5 2 0 row_00_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_02

theorem row_00_00_05_03 : b4RowContribution (![0, 0, 5, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 5, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_08
#print axioms Paper7MomentGapNumeric.row_00_00_05_03

theorem weighted_00_00_05_03 : b4RawGapContribution ![0, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 0 0 5 3 0 row_00_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_03

theorem row_00_00_05_04 : b4RowContribution (![0, 0, 5, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 5, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_09
#print axioms Paper7MomentGapNumeric.row_00_00_05_04

theorem weighted_00_00_05_04 : b4RawGapContribution ![0, 0, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 0 :=
      b4GapContribution_from_row 0 0 5 4 0 row_00_00_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_04

theorem row_00_00_05_05 : b4RowContribution (![0, 0, 5, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 5, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_10
#print axioms Paper7MomentGapNumeric.row_00_00_05_05

theorem weighted_00_00_05_05 : b4RawGapContribution ![0, 0, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 0 :=
      b4GapContribution_from_row 0 0 5 5 0 row_00_00_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_05

theorem row_00_00_05_06 : b4RowContribution (![0, 0, 5, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 5, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_11
#print axioms Paper7MomentGapNumeric.row_00_00_05_06

theorem weighted_00_00_05_06 : b4RawGapContribution ![0, 0, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 0 :=
      b4GapContribution_from_row 0 0 5 6 0 row_00_00_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_06

theorem row_00_00_05_07 : b4RowContribution (![0, 0, 5, 12] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 5, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_12
#print axioms Paper7MomentGapNumeric.row_00_00_05_07

theorem weighted_00_00_05_07 : b4RawGapContribution ![0, 0, 5, 7] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 2 :=
      b4GapContribution_from_row 0 0 5 7 2 row_00_00_05_07
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_07

theorem row_00_00_05_08 : b4RowContribution (![0, 0, 5, 13] : Fin 4 → ℕ) = 3 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 5, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_13
#print axioms Paper7MomentGapNumeric.row_00_00_05_08

theorem weighted_00_00_05_08 : b4RawGapContribution ![0, 0, 5, 8] = 36 := by
  calc
    b4RawGapContribution ![0, 0, 5, 8] = b4GapPatternWeight 0 5 8 * 3 :=
      b4GapContribution_from_row 0 0 5 8 3 row_00_00_05_08
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_08

theorem row_00_00_05_09 : b4RowContribution (![0, 0, 5, 14] : Fin 4 → ℕ) = 9 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 5, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_14
#print axioms Paper7MomentGapNumeric.row_00_00_05_09

theorem weighted_00_00_05_09 : b4RawGapContribution ![0, 0, 5, 9] = 108 := by
  calc
    b4RawGapContribution ![0, 0, 5, 9] = b4GapPatternWeight 0 5 9 * 9 :=
      b4GapContribution_from_row 0 0 5 9 9 row_00_00_05_09
    _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_09

theorem row_00_00_05_10 : b4RowContribution (![0, 0, 5, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 5, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_15
#print axioms Paper7MomentGapNumeric.row_00_00_05_10

theorem weighted_00_00_05_10 : b4RawGapContribution ![0, 0, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 10] = b4GapPatternWeight 0 5 10 * 0 :=
      b4GapContribution_from_row 0 0 5 10 0 row_00_00_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_10

theorem row_00_00_05_11 : b4RowContribution (![0, 0, 5, 16] : Fin 4 → ℕ) = 6 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 5, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_16
#print axioms Paper7MomentGapNumeric.row_00_00_05_11

theorem weighted_00_00_05_11 : b4RawGapContribution ![0, 0, 5, 11] = 72 := by
  calc
    b4RawGapContribution ![0, 0, 5, 11] = b4GapPatternWeight 0 5 11 * 6 :=
      b4GapContribution_from_row 0 0 5 11 6 row_00_00_05_11
    _ = 72 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_11

theorem row_00_00_05_12 : b4RowContribution (![0, 0, 5, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 5, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_17
#print axioms Paper7MomentGapNumeric.row_00_00_05_12

theorem weighted_00_00_05_12 : b4RawGapContribution ![0, 0, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 12] = b4GapPatternWeight 0 5 12 * 0 :=
      b4GapContribution_from_row 0 0 5 12 0 row_00_00_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_12

theorem row_00_00_05_13 : b4RowContribution (![0, 0, 5, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 5, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_18
#print axioms Paper7MomentGapNumeric.row_00_00_05_13

theorem weighted_00_00_05_13 : b4RawGapContribution ![0, 0, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 13] = b4GapPatternWeight 0 5 13 * 0 :=
      b4GapContribution_from_row 0 0 5 13 0 row_00_00_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_13

theorem row_00_00_05_14 : b4RowContribution (![0, 0, 5, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 5, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_19
#print axioms Paper7MomentGapNumeric.row_00_00_05_14

theorem weighted_00_00_05_14 : b4RawGapContribution ![0, 0, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 14] = b4GapPatternWeight 0 5 14 * 0 :=
      b4GapContribution_from_row 0 0 5 14 0 row_00_00_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_14

theorem row_00_00_05_15 : b4RowContribution (![0, 0, 5, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 5, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_20
#print axioms Paper7MomentGapNumeric.row_00_00_05_15

theorem weighted_00_00_05_15 : b4RawGapContribution ![0, 0, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 15] = b4GapPatternWeight 0 5 15 * 0 :=
      b4GapContribution_from_row 0 0 5 15 0 row_00_00_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_15

theorem row_00_00_05_16 : b4RowContribution (![0, 0, 5, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 5, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_21
#print axioms Paper7MomentGapNumeric.row_00_00_05_16

theorem weighted_00_00_05_16 : b4RawGapContribution ![0, 0, 5, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 16] = b4GapPatternWeight 0 5 16 * 0 :=
      b4GapContribution_from_row 0 0 5 16 0 row_00_00_05_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_16

theorem row_00_00_05_17 : b4RowContribution (![0, 0, 5, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 5, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_22
#print axioms Paper7MomentGapNumeric.row_00_00_05_17

theorem weighted_00_00_05_17 : b4RawGapContribution ![0, 0, 5, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 17] = b4GapPatternWeight 0 5 17 * 0 :=
      b4GapContribution_from_row 0 0 5 17 0 row_00_00_05_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_17

theorem row_00_00_05_18 : b4RowContribution (![0, 0, 5, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 5, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_23
#print axioms Paper7MomentGapNumeric.row_00_00_05_18

theorem weighted_00_00_05_18 : b4RawGapContribution ![0, 0, 5, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 18] = b4GapPatternWeight 0 5 18 * 0 :=
      b4GapContribution_from_row 0 0 5 18 0 row_00_00_05_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_18

theorem row_00_00_05_19 : b4RowContribution (![0, 0, 5, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 5, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_24
#print axioms Paper7MomentGapNumeric.row_00_00_05_19

theorem weighted_00_00_05_19 : b4RawGapContribution ![0, 0, 5, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 19] = b4GapPatternWeight 0 5 19 * 0 :=
      b4GapContribution_from_row 0 0 5 19 0 row_00_00_05_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_19

theorem row_00_00_05_20 : b4RowContribution (![0, 0, 5, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 5, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_25
#print axioms Paper7MomentGapNumeric.row_00_00_05_20

theorem weighted_00_00_05_20 : b4RawGapContribution ![0, 0, 5, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 20] = b4GapPatternWeight 0 5 20 * 0 :=
      b4GapContribution_from_row 0 0 5 20 0 row_00_00_05_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_20

theorem row_00_00_05_21 : b4RowContribution (![0, 0, 5, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 5, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_26
#print axioms Paper7MomentGapNumeric.row_00_00_05_21

theorem weighted_00_00_05_21 : b4RawGapContribution ![0, 0, 5, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 21] = b4GapPatternWeight 0 5 21 * 0 :=
      b4GapContribution_from_row 0 0 5 21 0 row_00_00_05_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_21

theorem row_00_00_05_22 : b4RowContribution (![0, 0, 5, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 5, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_27
#print axioms Paper7MomentGapNumeric.row_00_00_05_22

theorem weighted_00_00_05_22 : b4RawGapContribution ![0, 0, 5, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 22] = b4GapPatternWeight 0 5 22 * 0 :=
      b4GapContribution_from_row 0 0 5 22 0 row_00_00_05_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_22

theorem row_00_00_05_23 : b4RowContribution (![0, 0, 5, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 5, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_28
#print axioms Paper7MomentGapNumeric.row_00_00_05_23

theorem weighted_00_00_05_23 : b4RawGapContribution ![0, 0, 5, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 23] = b4GapPatternWeight 0 5 23 * 0 :=
      b4GapContribution_from_row 0 0 5 23 0 row_00_00_05_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_23

theorem row_00_00_05_24 : b4RowContribution (![0, 0, 5, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 5, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_29
#print axioms Paper7MomentGapNumeric.row_00_00_05_24

theorem weighted_00_00_05_24 : b4RawGapContribution ![0, 0, 5, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 24] = b4GapPatternWeight 0 5 24 * 0 :=
      b4GapContribution_from_row 0 0 5 24 0 row_00_00_05_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_24

theorem row_00_00_05_25 : b4RowContribution (![0, 0, 5, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 5, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_30
#print axioms Paper7MomentGapNumeric.row_00_00_05_25

theorem weighted_00_00_05_25 : b4RawGapContribution ![0, 0, 5, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 25] = b4GapPatternWeight 0 5 25 * 0 :=
      b4GapContribution_from_row 0 0 5 25 0 row_00_00_05_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_25

theorem row_00_00_05_26 : b4RowContribution (![0, 0, 5, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 5, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_31
#print axioms Paper7MomentGapNumeric.row_00_00_05_26

theorem weighted_00_00_05_26 : b4RawGapContribution ![0, 0, 5, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 26] = b4GapPatternWeight 0 5 26 * 0 :=
      b4GapContribution_from_row 0 0 5 26 0 row_00_00_05_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_26

theorem row_00_00_05_27 : b4RowContribution (![0, 0, 5, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨5, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 5, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_05_32
#print axioms Paper7MomentGapNumeric.row_00_00_05_27

theorem weighted_00_00_05_27 : b4RawGapContribution ![0, 0, 5, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 5, 27] = b4GapPatternWeight 0 5 27 * 0 :=
      b4GapContribution_from_row 0 0 5 27 0 row_00_00_05_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_05_27

def dvalues_00_00_05 : Fin 28 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 36, 108, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_05

theorem dblock_00_00_05 : b4GapPatternDBlock 0 0 5 = 240 := by
  calc
    b4GapPatternDBlock 0 0 5 = ∑ d : Fin 28, dvalues_00_00_05 d := by
      apply b4GapDBlock_of_rows 0 0 5 dvalues_00_00_05
      intro d
      fin_cases d
      · exact weighted_00_00_05_00
      · exact weighted_00_00_05_01
      · exact weighted_00_00_05_02
      · exact weighted_00_00_05_03
      · exact weighted_00_00_05_04
      · exact weighted_00_00_05_05
      · exact weighted_00_00_05_06
      · exact weighted_00_00_05_07
      · exact weighted_00_00_05_08
      · exact weighted_00_00_05_09
      · exact weighted_00_00_05_10
      · exact weighted_00_00_05_11
      · exact weighted_00_00_05_12
      · exact weighted_00_00_05_13
      · exact weighted_00_00_05_14
      · exact weighted_00_00_05_15
      · exact weighted_00_00_05_16
      · exact weighted_00_00_05_17
      · exact weighted_00_00_05_18
      · exact weighted_00_00_05_19
      · exact weighted_00_00_05_20
      · exact weighted_00_00_05_21
      · exact weighted_00_00_05_22
      · exact weighted_00_00_05_23
      · exact weighted_00_00_05_24
      · exact weighted_00_00_05_25
      · exact weighted_00_00_05_26
      · exact weighted_00_00_05_27
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_05

end Paper7MomentGapNumeric
