import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C06

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

theorem row_00_00_06_00 : b4RowContribution (![0, 0, 6, 6] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 6, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_06
#print axioms Paper7MomentGapNumeric.row_00_00_06_00

theorem weighted_00_00_06_00 : b4RawGapContribution ![0, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 0 0 6 0 0 row_00_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_00

theorem row_00_00_06_01 : b4RowContribution (![0, 0, 6, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 6, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_07
#print axioms Paper7MomentGapNumeric.row_00_00_06_01

theorem weighted_00_00_06_01 : b4RawGapContribution ![0, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 0 0 6 1 0 row_00_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_01

theorem row_00_00_06_02 : b4RowContribution (![0, 0, 6, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 6, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_08
#print axioms Paper7MomentGapNumeric.row_00_00_06_02

theorem weighted_00_00_06_02 : b4RawGapContribution ![0, 0, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 0 :=
      b4GapContribution_from_row 0 0 6 2 0 row_00_00_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_02

theorem row_00_00_06_03 : b4RowContribution (![0, 0, 6, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 6, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_09
#print axioms Paper7MomentGapNumeric.row_00_00_06_03

theorem weighted_00_00_06_03 : b4RawGapContribution ![0, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 0 0 6 3 0 row_00_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_03

theorem row_00_00_06_04 : b4RowContribution (![0, 0, 6, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 6, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_10
#print axioms Paper7MomentGapNumeric.row_00_00_06_04

theorem weighted_00_00_06_04 : b4RawGapContribution ![0, 0, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 0 :=
      b4GapContribution_from_row 0 0 6 4 0 row_00_00_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_04

theorem row_00_00_06_05 : b4RowContribution (![0, 0, 6, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 6, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_11
#print axioms Paper7MomentGapNumeric.row_00_00_06_05

theorem weighted_00_00_06_05 : b4RawGapContribution ![0, 0, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 0 :=
      b4GapContribution_from_row 0 0 6 5 0 row_00_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_05

theorem row_00_00_06_06 : b4RowContribution (![0, 0, 6, 12] : Fin 4 → ℕ) = 7 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 6, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_12
#print axioms Paper7MomentGapNumeric.row_00_00_06_06

theorem weighted_00_00_06_06 : b4RawGapContribution ![0, 0, 6, 6] = 84 := by
  calc
    b4RawGapContribution ![0, 0, 6, 6] = b4GapPatternWeight 0 6 6 * 7 :=
      b4GapContribution_from_row 0 0 6 6 7 row_00_00_06_06
    _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_06

theorem row_00_00_06_07 : b4RowContribution (![0, 0, 6, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 6, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_13
#print axioms Paper7MomentGapNumeric.row_00_00_06_07

theorem weighted_00_00_06_07 : b4RawGapContribution ![0, 0, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 7] = b4GapPatternWeight 0 6 7 * 0 :=
      b4GapContribution_from_row 0 0 6 7 0 row_00_00_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_07

theorem row_00_00_06_08 : b4RowContribution (![0, 0, 6, 14] : Fin 4 → ℕ) = 17 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 6, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_14
#print axioms Paper7MomentGapNumeric.row_00_00_06_08

theorem weighted_00_00_06_08 : b4RawGapContribution ![0, 0, 6, 8] = 204 := by
  calc
    b4RawGapContribution ![0, 0, 6, 8] = b4GapPatternWeight 0 6 8 * 17 :=
      b4GapContribution_from_row 0 0 6 8 17 row_00_00_06_08
    _ = 204 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_08

theorem row_00_00_06_09 : b4RowContribution (![0, 0, 6, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 6, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_15
#print axioms Paper7MomentGapNumeric.row_00_00_06_09

theorem weighted_00_00_06_09 : b4RawGapContribution ![0, 0, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 9] = b4GapPatternWeight 0 6 9 * 0 :=
      b4GapContribution_from_row 0 0 6 9 0 row_00_00_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_09

theorem row_00_00_06_10 : b4RowContribution (![0, 0, 6, 16] : Fin 4 → ℕ) = 7 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 6, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_16
#print axioms Paper7MomentGapNumeric.row_00_00_06_10

theorem weighted_00_00_06_10 : b4RawGapContribution ![0, 0, 6, 10] = 84 := by
  calc
    b4RawGapContribution ![0, 0, 6, 10] = b4GapPatternWeight 0 6 10 * 7 :=
      b4GapContribution_from_row 0 0 6 10 7 row_00_00_06_10
    _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_10

theorem row_00_00_06_11 : b4RowContribution (![0, 0, 6, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 6, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_17
#print axioms Paper7MomentGapNumeric.row_00_00_06_11

theorem weighted_00_00_06_11 : b4RawGapContribution ![0, 0, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 11] = b4GapPatternWeight 0 6 11 * 0 :=
      b4GapContribution_from_row 0 0 6 11 0 row_00_00_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_11

theorem row_00_00_06_12 : b4RowContribution (![0, 0, 6, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 6, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_18
#print axioms Paper7MomentGapNumeric.row_00_00_06_12

theorem weighted_00_00_06_12 : b4RawGapContribution ![0, 0, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 12] = b4GapPatternWeight 0 6 12 * 0 :=
      b4GapContribution_from_row 0 0 6 12 0 row_00_00_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_12

theorem row_00_00_06_13 : b4RowContribution (![0, 0, 6, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 6, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_19
#print axioms Paper7MomentGapNumeric.row_00_00_06_13

theorem weighted_00_00_06_13 : b4RawGapContribution ![0, 0, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 13] = b4GapPatternWeight 0 6 13 * 0 :=
      b4GapContribution_from_row 0 0 6 13 0 row_00_00_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_13

theorem row_00_00_06_14 : b4RowContribution (![0, 0, 6, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 6, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_20
#print axioms Paper7MomentGapNumeric.row_00_00_06_14

theorem weighted_00_00_06_14 : b4RawGapContribution ![0, 0, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 14] = b4GapPatternWeight 0 6 14 * 0 :=
      b4GapContribution_from_row 0 0 6 14 0 row_00_00_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_14

theorem row_00_00_06_15 : b4RowContribution (![0, 0, 6, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 6, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_21
#print axioms Paper7MomentGapNumeric.row_00_00_06_15

theorem weighted_00_00_06_15 : b4RawGapContribution ![0, 0, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 15] = b4GapPatternWeight 0 6 15 * 0 :=
      b4GapContribution_from_row 0 0 6 15 0 row_00_00_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_15

theorem row_00_00_06_16 : b4RowContribution (![0, 0, 6, 22] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 6, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_22
#print axioms Paper7MomentGapNumeric.row_00_00_06_16

theorem weighted_00_00_06_16 : b4RawGapContribution ![0, 0, 6, 16] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 6, 16] = b4GapPatternWeight 0 6 16 * 5 :=
      b4GapContribution_from_row 0 0 6 16 5 row_00_00_06_16
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_16

theorem row_00_00_06_17 : b4RowContribution (![0, 0, 6, 23] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 6, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_23
#print axioms Paper7MomentGapNumeric.row_00_00_06_17

theorem weighted_00_00_06_17 : b4RawGapContribution ![0, 0, 6, 17] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 6, 17] = b4GapPatternWeight 0 6 17 * 5 :=
      b4GapContribution_from_row 0 0 6 17 5 row_00_00_06_17
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_17

theorem row_00_00_06_18 : b4RowContribution (![0, 0, 6, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 6, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_24
#print axioms Paper7MomentGapNumeric.row_00_00_06_18

theorem weighted_00_00_06_18 : b4RawGapContribution ![0, 0, 6, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 18] = b4GapPatternWeight 0 6 18 * 0 :=
      b4GapContribution_from_row 0 0 6 18 0 row_00_00_06_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_18

theorem row_00_00_06_19 : b4RowContribution (![0, 0, 6, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 6, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_25
#print axioms Paper7MomentGapNumeric.row_00_00_06_19

theorem weighted_00_00_06_19 : b4RawGapContribution ![0, 0, 6, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 19] = b4GapPatternWeight 0 6 19 * 0 :=
      b4GapContribution_from_row 0 0 6 19 0 row_00_00_06_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_19

theorem row_00_00_06_20 : b4RowContribution (![0, 0, 6, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 6, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_26
#print axioms Paper7MomentGapNumeric.row_00_00_06_20

theorem weighted_00_00_06_20 : b4RawGapContribution ![0, 0, 6, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 20] = b4GapPatternWeight 0 6 20 * 0 :=
      b4GapContribution_from_row 0 0 6 20 0 row_00_00_06_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_20

theorem row_00_00_06_21 : b4RowContribution (![0, 0, 6, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 6, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_27
#print axioms Paper7MomentGapNumeric.row_00_00_06_21

theorem weighted_00_00_06_21 : b4RawGapContribution ![0, 0, 6, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 21] = b4GapPatternWeight 0 6 21 * 0 :=
      b4GapContribution_from_row 0 0 6 21 0 row_00_00_06_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_21

theorem row_00_00_06_22 : b4RowContribution (![0, 0, 6, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 6, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_28
#print axioms Paper7MomentGapNumeric.row_00_00_06_22

theorem weighted_00_00_06_22 : b4RawGapContribution ![0, 0, 6, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 22] = b4GapPatternWeight 0 6 22 * 0 :=
      b4GapContribution_from_row 0 0 6 22 0 row_00_00_06_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_22

theorem row_00_00_06_23 : b4RowContribution (![0, 0, 6, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 6, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_29
#print axioms Paper7MomentGapNumeric.row_00_00_06_23

theorem weighted_00_00_06_23 : b4RawGapContribution ![0, 0, 6, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 23] = b4GapPatternWeight 0 6 23 * 0 :=
      b4GapContribution_from_row 0 0 6 23 0 row_00_00_06_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_23

theorem row_00_00_06_24 : b4RowContribution (![0, 0, 6, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 6, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_30
#print axioms Paper7MomentGapNumeric.row_00_00_06_24

theorem weighted_00_00_06_24 : b4RawGapContribution ![0, 0, 6, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 24] = b4GapPatternWeight 0 6 24 * 0 :=
      b4GapContribution_from_row 0 0 6 24 0 row_00_00_06_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_24

theorem row_00_00_06_25 : b4RowContribution (![0, 0, 6, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨6, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 6, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_06_31
#print axioms Paper7MomentGapNumeric.row_00_00_06_25

theorem weighted_00_00_06_25 : b4RawGapContribution ![0, 0, 6, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 6, 25] = b4GapPatternWeight 0 6 25 * 0 :=
      b4GapContribution_from_row 0 0 6 25 0 row_00_00_06_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_06_25

def dvalues_00_00_06 : Fin 26 → ℕ := ![0, 0, 0, 0, 0, 0, 84, 0, 204, 0, 84, 0, 0, 0, 0, 0, 60, 60, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_06

theorem dblock_00_00_06 : b4GapPatternDBlock 0 0 6 = 492 := by
  calc
    b4GapPatternDBlock 0 0 6 = ∑ d : Fin 26, dvalues_00_00_06 d := by
      apply b4GapDBlock_of_rows 0 0 6 dvalues_00_00_06
      intro d
      fin_cases d
      · exact weighted_00_00_06_00
      · exact weighted_00_00_06_01
      · exact weighted_00_00_06_02
      · exact weighted_00_00_06_03
      · exact weighted_00_00_06_04
      · exact weighted_00_00_06_05
      · exact weighted_00_00_06_06
      · exact weighted_00_00_06_07
      · exact weighted_00_00_06_08
      · exact weighted_00_00_06_09
      · exact weighted_00_00_06_10
      · exact weighted_00_00_06_11
      · exact weighted_00_00_06_12
      · exact weighted_00_00_06_13
      · exact weighted_00_00_06_14
      · exact weighted_00_00_06_15
      · exact weighted_00_00_06_16
      · exact weighted_00_00_06_17
      · exact weighted_00_00_06_18
      · exact weighted_00_00_06_19
      · exact weighted_00_00_06_20
      · exact weighted_00_00_06_21
      · exact weighted_00_00_06_22
      · exact weighted_00_00_06_23
      · exact weighted_00_00_06_24
      · exact weighted_00_00_06_25
    _ = 492 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_06

end Paper7MomentGapNumeric
