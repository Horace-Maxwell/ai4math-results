import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C03
import Research.Backfill.Paper7.MomentB4MultiQRowPrototype

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

theorem row_00_00_03_00 : b4RowContribution (![0, 0, 3, 3] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨3, by decide⟩⟩ = (![0, 0, 3, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_03
#print axioms Paper7MomentGapNumeric.row_00_00_03_00

theorem weighted_00_00_03_00 : b4RawGapContribution ![0, 0, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 0] = b4GapPatternWeight 0 3 0 * 0 :=
      b4GapContribution_from_row 0 0 3 0 0 row_00_00_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_00

theorem row_00_00_03_01 : b4RowContribution (![0, 0, 3, 4] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨4, by decide⟩⟩ = (![0, 0, 3, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_04
#print axioms Paper7MomentGapNumeric.row_00_00_03_01

theorem weighted_00_00_03_01 : b4RawGapContribution ![0, 0, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 1] = b4GapPatternWeight 0 3 1 * 0 :=
      b4GapContribution_from_row 0 0 3 1 0 row_00_00_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_01

theorem row_00_00_03_02 : b4RowContribution (![0, 0, 3, 5] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 3, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_05
#print axioms Paper7MomentGapNumeric.row_00_00_03_02

theorem weighted_00_00_03_02 : b4RawGapContribution ![0, 0, 3, 2] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 3, 2] = b4GapPatternWeight 0 3 2 * 2 :=
      b4GapContribution_from_row 0 0 3 2 2 row_00_00_03_02
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_02

theorem row_00_00_03_03 : b4RowContribution (![0, 0, 3, 6] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 3, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_06
#print axioms Paper7MomentGapNumeric.row_00_00_03_03

theorem weighted_00_00_03_03 : b4RawGapContribution ![0, 0, 3, 3] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 3, 3] = b4GapPatternWeight 0 3 3 * 5 :=
      b4GapContribution_from_row 0 0 3 3 5 row_00_00_03_03
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_03

theorem row_00_00_03_04 : b4RowContribution (![0, 0, 3, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 3, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_07
#print axioms Paper7MomentGapNumeric.row_00_00_03_04

theorem weighted_00_00_03_04 : b4RawGapContribution ![0, 0, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 4] = b4GapPatternWeight 0 3 4 * 0 :=
      b4GapContribution_from_row 0 0 3 4 0 row_00_00_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_04

theorem row_00_00_03_05 : b4RowContribution (![0, 0, 3, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 3, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_08
#print axioms Paper7MomentGapNumeric.row_00_00_03_05

theorem weighted_00_00_03_05 : b4RawGapContribution ![0, 0, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 5] = b4GapPatternWeight 0 3 5 * 0 :=
      b4GapContribution_from_row 0 0 3 5 0 row_00_00_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_05

theorem row_00_00_03_06 : b4RowContribution (![0, 0, 3, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 3, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_09
#print axioms Paper7MomentGapNumeric.row_00_00_03_06

theorem weighted_00_00_03_06 : b4RawGapContribution ![0, 0, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 6] = b4GapPatternWeight 0 3 6 * 0 :=
      b4GapContribution_from_row 0 0 3 6 0 row_00_00_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_06

theorem row_00_00_03_07 : b4RowContribution (![0, 0, 3, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 3, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_10
#print axioms Paper7MomentGapNumeric.row_00_00_03_07

theorem weighted_00_00_03_07 : b4RawGapContribution ![0, 0, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 7] = b4GapPatternWeight 0 3 7 * 0 :=
      b4GapContribution_from_row 0 0 3 7 0 row_00_00_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_07

theorem row_00_00_03_08 : b4RowContribution (![0, 0, 3, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 3, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_11
#print axioms Paper7MomentGapNumeric.row_00_00_03_08

theorem weighted_00_00_03_08 : b4RawGapContribution ![0, 0, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 8] = b4GapPatternWeight 0 3 8 * 0 :=
      b4GapContribution_from_row 0 0 3 8 0 row_00_00_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_08

theorem row_00_00_03_09 : b4RowContribution (![0, 0, 3, 12] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 3, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_12
#print axioms Paper7MomentGapNumeric.row_00_00_03_09

theorem weighted_00_00_03_09 : b4RawGapContribution ![0, 0, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 9] = b4GapPatternWeight 0 3 9 * 0 :=
      b4GapContribution_from_row 0 0 3 9 0 row_00_00_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_09

theorem row_00_00_03_10 : b4RowContribution (![0, 0, 3, 13] : Fin 4 → ℕ) = 8 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 3, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_13
#print axioms Paper7MomentGapNumeric.row_00_00_03_10

theorem weighted_00_00_03_10 : b4RawGapContribution ![0, 0, 3, 10] = 96 := by
  calc
    b4RawGapContribution ![0, 0, 3, 10] = b4GapPatternWeight 0 3 10 * 8 :=
      b4GapContribution_from_row 0 0 3 10 8 row_00_00_03_10
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_10

theorem row_00_00_03_11 : b4RowContribution (![0, 0, 3, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 3, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_14
#print axioms Paper7MomentGapNumeric.row_00_00_03_11

theorem weighted_00_00_03_11 : b4RawGapContribution ![0, 0, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 11] = b4GapPatternWeight 0 3 11 * 0 :=
      b4GapContribution_from_row 0 0 3 11 0 row_00_00_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_11

theorem weighted_00_00_03_12 : b4RawGapContribution ![0, 0, 3, 12] = 108 :=
  Paper7MomentNumericPrototype.multi_gap_contribution
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_12

theorem row_00_00_03_13 : b4RowContribution (![0, 0, 3, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 3, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_16
#print axioms Paper7MomentGapNumeric.row_00_00_03_13

theorem weighted_00_00_03_13 : b4RawGapContribution ![0, 0, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 13] = b4GapPatternWeight 0 3 13 * 0 :=
      b4GapContribution_from_row 0 0 3 13 0 row_00_00_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_13

theorem row_00_00_03_14 : b4RowContribution (![0, 0, 3, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 3, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_17
#print axioms Paper7MomentGapNumeric.row_00_00_03_14

theorem weighted_00_00_03_14 : b4RawGapContribution ![0, 0, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 14] = b4GapPatternWeight 0 3 14 * 0 :=
      b4GapContribution_from_row 0 0 3 14 0 row_00_00_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_14

theorem row_00_00_03_15 : b4RowContribution (![0, 0, 3, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 3, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_18
#print axioms Paper7MomentGapNumeric.row_00_00_03_15

theorem weighted_00_00_03_15 : b4RawGapContribution ![0, 0, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 15] = b4GapPatternWeight 0 3 15 * 0 :=
      b4GapContribution_from_row 0 0 3 15 0 row_00_00_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_15

theorem row_00_00_03_16 : b4RowContribution (![0, 0, 3, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 3, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_19
#print axioms Paper7MomentGapNumeric.row_00_00_03_16

theorem weighted_00_00_03_16 : b4RawGapContribution ![0, 0, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 16] = b4GapPatternWeight 0 3 16 * 0 :=
      b4GapContribution_from_row 0 0 3 16 0 row_00_00_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_16

theorem row_00_00_03_17 : b4RowContribution (![0, 0, 3, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 3, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_20
#print axioms Paper7MomentGapNumeric.row_00_00_03_17

theorem weighted_00_00_03_17 : b4RawGapContribution ![0, 0, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 17] = b4GapPatternWeight 0 3 17 * 0 :=
      b4GapContribution_from_row 0 0 3 17 0 row_00_00_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_17

theorem row_00_00_03_18 : b4RowContribution (![0, 0, 3, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 3, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_21
#print axioms Paper7MomentGapNumeric.row_00_00_03_18

theorem weighted_00_00_03_18 : b4RawGapContribution ![0, 0, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 18] = b4GapPatternWeight 0 3 18 * 0 :=
      b4GapContribution_from_row 0 0 3 18 0 row_00_00_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_18

theorem row_00_00_03_19 : b4RowContribution (![0, 0, 3, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 3, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_22
#print axioms Paper7MomentGapNumeric.row_00_00_03_19

theorem weighted_00_00_03_19 : b4RawGapContribution ![0, 0, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 19] = b4GapPatternWeight 0 3 19 * 0 :=
      b4GapContribution_from_row 0 0 3 19 0 row_00_00_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_19

theorem row_00_00_03_20 : b4RowContribution (![0, 0, 3, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 3, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_23
#print axioms Paper7MomentGapNumeric.row_00_00_03_20

theorem weighted_00_00_03_20 : b4RawGapContribution ![0, 0, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 20] = b4GapPatternWeight 0 3 20 * 0 :=
      b4GapContribution_from_row 0 0 3 20 0 row_00_00_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_20

theorem row_00_00_03_21 : b4RowContribution (![0, 0, 3, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 3, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_24
#print axioms Paper7MomentGapNumeric.row_00_00_03_21

theorem weighted_00_00_03_21 : b4RawGapContribution ![0, 0, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 21] = b4GapPatternWeight 0 3 21 * 0 :=
      b4GapContribution_from_row 0 0 3 21 0 row_00_00_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_21

theorem row_00_00_03_22 : b4RowContribution (![0, 0, 3, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 3, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_25
#print axioms Paper7MomentGapNumeric.row_00_00_03_22

theorem weighted_00_00_03_22 : b4RawGapContribution ![0, 0, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 22] = b4GapPatternWeight 0 3 22 * 0 :=
      b4GapContribution_from_row 0 0 3 22 0 row_00_00_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_22

theorem row_00_00_03_23 : b4RowContribution (![0, 0, 3, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 3, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_26
#print axioms Paper7MomentGapNumeric.row_00_00_03_23

theorem weighted_00_00_03_23 : b4RawGapContribution ![0, 0, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 23] = b4GapPatternWeight 0 3 23 * 0 :=
      b4GapContribution_from_row 0 0 3 23 0 row_00_00_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_23

theorem row_00_00_03_24 : b4RowContribution (![0, 0, 3, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 3, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_27
#print axioms Paper7MomentGapNumeric.row_00_00_03_24

theorem weighted_00_00_03_24 : b4RawGapContribution ![0, 0, 3, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 24] = b4GapPatternWeight 0 3 24 * 0 :=
      b4GapContribution_from_row 0 0 3 24 0 row_00_00_03_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_24

theorem row_00_00_03_25 : b4RowContribution (![0, 0, 3, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 3, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_28
#print axioms Paper7MomentGapNumeric.row_00_00_03_25

theorem weighted_00_00_03_25 : b4RawGapContribution ![0, 0, 3, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 25] = b4GapPatternWeight 0 3 25 * 0 :=
      b4GapContribution_from_row 0 0 3 25 0 row_00_00_03_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_25

theorem row_00_00_03_26 : b4RowContribution (![0, 0, 3, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 3, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_29
#print axioms Paper7MomentGapNumeric.row_00_00_03_26

theorem weighted_00_00_03_26 : b4RawGapContribution ![0, 0, 3, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 26] = b4GapPatternWeight 0 3 26 * 0 :=
      b4GapContribution_from_row 0 0 3 26 0 row_00_00_03_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_26

theorem row_00_00_03_27 : b4RowContribution (![0, 0, 3, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 3, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_30
#print axioms Paper7MomentGapNumeric.row_00_00_03_27

theorem weighted_00_00_03_27 : b4RawGapContribution ![0, 0, 3, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 27] = b4GapPatternWeight 0 3 27 * 0 :=
      b4GapContribution_from_row 0 0 3 27 0 row_00_00_03_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_27

theorem row_00_00_03_28 : b4RowContribution (![0, 0, 3, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 3, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_31
#print axioms Paper7MomentGapNumeric.row_00_00_03_28

theorem weighted_00_00_03_28 : b4RawGapContribution ![0, 0, 3, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 28] = b4GapPatternWeight 0 3 28 * 0 :=
      b4GapContribution_from_row 0 0 3 28 0 row_00_00_03_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_28

theorem row_00_00_03_29 : b4RowContribution (![0, 0, 3, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 3, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_32
#print axioms Paper7MomentGapNumeric.row_00_00_03_29

theorem weighted_00_00_03_29 : b4RawGapContribution ![0, 0, 3, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 29] = b4GapPatternWeight 0 3 29 * 0 :=
      b4GapContribution_from_row 0 0 3 29 0 row_00_00_03_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_29

theorem row_00_00_03_30 : b4RowContribution (![0, 0, 3, 33] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨33, by decide⟩⟩ = (![0, 0, 3, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_33
#print axioms Paper7MomentGapNumeric.row_00_00_03_30

theorem weighted_00_00_03_30 : b4RawGapContribution ![0, 0, 3, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 30] = b4GapPatternWeight 0 3 30 * 0 :=
      b4GapContribution_from_row 0 0 3 30 0 row_00_00_03_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_30

theorem row_00_00_03_31 : b4RowContribution (![0, 0, 3, 34] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨34, by decide⟩⟩ = (![0, 0, 3, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_34
#print axioms Paper7MomentGapNumeric.row_00_00_03_31

theorem weighted_00_00_03_31 : b4RawGapContribution ![0, 0, 3, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 3, 31] = b4GapPatternWeight 0 3 31 * 0 :=
      b4GapContribution_from_row 0 0 3 31 0 row_00_00_03_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_03_31

def dvalues_00_00_03 : Fin 32 → ℕ := ![0, 0, 24, 60, 0, 0, 0, 0, 0, 0, 96, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_03

theorem dblock_00_00_03 : b4GapPatternDBlock 0 0 3 = 288 := by
  calc
    b4GapPatternDBlock 0 0 3 = ∑ d : Fin 32, dvalues_00_00_03 d := by
      apply b4GapDBlock_of_rows 0 0 3 dvalues_00_00_03
      intro d
      fin_cases d
      · exact weighted_00_00_03_00
      · exact weighted_00_00_03_01
      · exact weighted_00_00_03_02
      · exact weighted_00_00_03_03
      · exact weighted_00_00_03_04
      · exact weighted_00_00_03_05
      · exact weighted_00_00_03_06
      · exact weighted_00_00_03_07
      · exact weighted_00_00_03_08
      · exact weighted_00_00_03_09
      · exact weighted_00_00_03_10
      · exact weighted_00_00_03_11
      · exact weighted_00_00_03_12
      · exact weighted_00_00_03_13
      · exact weighted_00_00_03_14
      · exact weighted_00_00_03_15
      · exact weighted_00_00_03_16
      · exact weighted_00_00_03_17
      · exact weighted_00_00_03_18
      · exact weighted_00_00_03_19
      · exact weighted_00_00_03_20
      · exact weighted_00_00_03_21
      · exact weighted_00_00_03_22
      · exact weighted_00_00_03_23
      · exact weighted_00_00_03_24
      · exact weighted_00_00_03_25
      · exact weighted_00_00_03_26
      · exact weighted_00_00_03_27
      · exact weighted_00_00_03_28
      · exact weighted_00_00_03_29
      · exact weighted_00_00_03_30
      · exact weighted_00_00_03_31
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_03

end Paper7MomentGapNumeric
