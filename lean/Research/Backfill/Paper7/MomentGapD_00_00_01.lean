import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C01

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

theorem row_00_00_01_00 : b4RowContribution (![0, 0, 1, 1] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨1, by decide⟩⟩ = (![0, 0, 1, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_01
#print axioms Paper7MomentGapNumeric.row_00_00_01_00

theorem weighted_00_00_01_00 : b4RawGapContribution ![0, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 0 0 1 0 0 row_00_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_00

theorem row_00_00_01_01 : b4RowContribution (![0, 0, 1, 2] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨2, by decide⟩⟩ = (![0, 0, 1, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_02
#print axioms Paper7MomentGapNumeric.row_00_00_01_01

theorem weighted_00_00_01_01 : b4RawGapContribution ![0, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 0 0 1 1 0 row_00_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_01

theorem row_00_00_01_02 : b4RowContribution (![0, 0, 1, 3] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨3, by decide⟩⟩ = (![0, 0, 1, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_03
#print axioms Paper7MomentGapNumeric.row_00_00_01_02

theorem weighted_00_00_01_02 : b4RawGapContribution ![0, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 0 0 1 2 0 row_00_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_02

theorem row_00_00_01_03 : b4RowContribution (![0, 0, 1, 4] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨4, by decide⟩⟩ = (![0, 0, 1, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_04
#print axioms Paper7MomentGapNumeric.row_00_00_01_03

theorem weighted_00_00_01_03 : b4RawGapContribution ![0, 0, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 0 :=
      b4GapContribution_from_row 0 0 1 3 0 row_00_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_03

theorem row_00_00_01_04 : b4RowContribution (![0, 0, 1, 5] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 1, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_05
#print axioms Paper7MomentGapNumeric.row_00_00_01_04

theorem weighted_00_00_01_04 : b4RawGapContribution ![0, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 0 0 1 4 0 row_00_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_04

theorem row_00_00_01_05 : b4RowContribution (![0, 0, 1, 6] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 1, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_06
#print axioms Paper7MomentGapNumeric.row_00_00_01_05

theorem weighted_00_00_01_05 : b4RawGapContribution ![0, 0, 1, 5] = 12 := by
  calc
    b4RawGapContribution ![0, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 1 :=
      b4GapContribution_from_row 0 0 1 5 1 row_00_00_01_05
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_05

theorem row_00_00_01_06 : b4RowContribution (![0, 0, 1, 7] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 1, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_07
#print axioms Paper7MomentGapNumeric.row_00_00_01_06

theorem weighted_00_00_01_06 : b4RawGapContribution ![0, 0, 1, 6] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 2 :=
      b4GapContribution_from_row 0 0 1 6 2 row_00_00_01_06
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_06

theorem row_00_00_01_07 : b4RowContribution (![0, 0, 1, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 1, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_08
#print axioms Paper7MomentGapNumeric.row_00_00_01_07

theorem weighted_00_00_01_07 : b4RawGapContribution ![0, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 0 0 1 7 0 row_00_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_07

theorem row_00_00_01_08 : b4RowContribution (![0, 0, 1, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 1, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_09
#print axioms Paper7MomentGapNumeric.row_00_00_01_08

theorem weighted_00_00_01_08 : b4RawGapContribution ![0, 0, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 8] = b4GapPatternWeight 0 1 8 * 0 :=
      b4GapContribution_from_row 0 0 1 8 0 row_00_00_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_08

theorem row_00_00_01_09 : b4RowContribution (![0, 0, 1, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 1, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_10
#print axioms Paper7MomentGapNumeric.row_00_00_01_09

theorem weighted_00_00_01_09 : b4RawGapContribution ![0, 0, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 9] = b4GapPatternWeight 0 1 9 * 0 :=
      b4GapContribution_from_row 0 0 1 9 0 row_00_00_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_09

theorem row_00_00_01_10 : b4RowContribution (![0, 0, 1, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 1, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_11
#print axioms Paper7MomentGapNumeric.row_00_00_01_10

theorem weighted_00_00_01_10 : b4RawGapContribution ![0, 0, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 10] = b4GapPatternWeight 0 1 10 * 0 :=
      b4GapContribution_from_row 0 0 1 10 0 row_00_00_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_10

theorem row_00_00_01_11 : b4RowContribution (![0, 0, 1, 12] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 1, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_12
#print axioms Paper7MomentGapNumeric.row_00_00_01_11

theorem weighted_00_00_01_11 : b4RawGapContribution ![0, 0, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 11] = b4GapPatternWeight 0 1 11 * 0 :=
      b4GapContribution_from_row 0 0 1 11 0 row_00_00_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_11

theorem row_00_00_01_12 : b4RowContribution (![0, 0, 1, 13] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 1, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_13
#print axioms Paper7MomentGapNumeric.row_00_00_01_12

theorem weighted_00_00_01_12 : b4RawGapContribution ![0, 0, 1, 12] = 12 := by
  calc
    b4RawGapContribution ![0, 0, 1, 12] = b4GapPatternWeight 0 1 12 * 1 :=
      b4GapContribution_from_row 0 0 1 12 1 row_00_00_01_12
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_12

theorem row_00_00_01_13 : b4RowContribution (![0, 0, 1, 14] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 1, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_14
#print axioms Paper7MomentGapNumeric.row_00_00_01_13

theorem weighted_00_00_01_13 : b4RawGapContribution ![0, 0, 1, 13] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 13] = b4GapPatternWeight 0 1 13 * 2 :=
      b4GapContribution_from_row 0 0 1 13 2 row_00_00_01_13
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_13

theorem row_00_00_01_14 : b4RowContribution (![0, 0, 1, 15] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 1, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_15
#print axioms Paper7MomentGapNumeric.row_00_00_01_14

theorem weighted_00_00_01_14 : b4RawGapContribution ![0, 0, 1, 14] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 14] = b4GapPatternWeight 0 1 14 * 2 :=
      b4GapContribution_from_row 0 0 1 14 2 row_00_00_01_14
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_14

theorem row_00_00_01_15 : b4RowContribution (![0, 0, 1, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 1, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_16
#print axioms Paper7MomentGapNumeric.row_00_00_01_15

theorem weighted_00_00_01_15 : b4RawGapContribution ![0, 0, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 15] = b4GapPatternWeight 0 1 15 * 0 :=
      b4GapContribution_from_row 0 0 1 15 0 row_00_00_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_15

theorem row_00_00_01_16 : b4RowContribution (![0, 0, 1, 17] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 1, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_17
#print axioms Paper7MomentGapNumeric.row_00_00_01_16

theorem weighted_00_00_01_16 : b4RawGapContribution ![0, 0, 1, 16] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 16] = b4GapPatternWeight 0 1 16 * 2 :=
      b4GapContribution_from_row 0 0 1 16 2 row_00_00_01_16
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_16

theorem row_00_00_01_17 : b4RowContribution (![0, 0, 1, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 1, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_18
#print axioms Paper7MomentGapNumeric.row_00_00_01_17

theorem weighted_00_00_01_17 : b4RawGapContribution ![0, 0, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 17] = b4GapPatternWeight 0 1 17 * 0 :=
      b4GapContribution_from_row 0 0 1 17 0 row_00_00_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_17

theorem row_00_00_01_18 : b4RowContribution (![0, 0, 1, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 1, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_19
#print axioms Paper7MomentGapNumeric.row_00_00_01_18

theorem weighted_00_00_01_18 : b4RawGapContribution ![0, 0, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 18] = b4GapPatternWeight 0 1 18 * 0 :=
      b4GapContribution_from_row 0 0 1 18 0 row_00_00_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_18

theorem row_00_00_01_19 : b4RowContribution (![0, 0, 1, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 1, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_20
#print axioms Paper7MomentGapNumeric.row_00_00_01_19

theorem weighted_00_00_01_19 : b4RawGapContribution ![0, 0, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 19] = b4GapPatternWeight 0 1 19 * 0 :=
      b4GapContribution_from_row 0 0 1 19 0 row_00_00_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_19

theorem row_00_00_01_20 : b4RowContribution (![0, 0, 1, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 1, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_21
#print axioms Paper7MomentGapNumeric.row_00_00_01_20

theorem weighted_00_00_01_20 : b4RawGapContribution ![0, 0, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 20] = b4GapPatternWeight 0 1 20 * 0 :=
      b4GapContribution_from_row 0 0 1 20 0 row_00_00_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_20

theorem row_00_00_01_21 : b4RowContribution (![0, 0, 1, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 1, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_22
#print axioms Paper7MomentGapNumeric.row_00_00_01_21

theorem weighted_00_00_01_21 : b4RawGapContribution ![0, 0, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 21] = b4GapPatternWeight 0 1 21 * 0 :=
      b4GapContribution_from_row 0 0 1 21 0 row_00_00_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_21

theorem row_00_00_01_22 : b4RowContribution (![0, 0, 1, 23] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 1, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_23
#print axioms Paper7MomentGapNumeric.row_00_00_01_22

theorem weighted_00_00_01_22 : b4RawGapContribution ![0, 0, 1, 22] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 22] = b4GapPatternWeight 0 1 22 * 2 :=
      b4GapContribution_from_row 0 0 1 22 2 row_00_00_01_22
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_22

theorem row_00_00_01_23 : b4RowContribution (![0, 0, 1, 24] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 1, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_24
#print axioms Paper7MomentGapNumeric.row_00_00_01_23

theorem weighted_00_00_01_23 : b4RawGapContribution ![0, 0, 1, 23] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 1, 23] = b4GapPatternWeight 0 1 23 * 2 :=
      b4GapContribution_from_row 0 0 1 23 2 row_00_00_01_23
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_23

theorem row_00_00_01_24 : b4RowContribution (![0, 0, 1, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 1, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_25
#print axioms Paper7MomentGapNumeric.row_00_00_01_24

theorem weighted_00_00_01_24 : b4RawGapContribution ![0, 0, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 24] = b4GapPatternWeight 0 1 24 * 0 :=
      b4GapContribution_from_row 0 0 1 24 0 row_00_00_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_24

theorem row_00_00_01_25 : b4RowContribution (![0, 0, 1, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 1, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_26
#print axioms Paper7MomentGapNumeric.row_00_00_01_25

theorem weighted_00_00_01_25 : b4RawGapContribution ![0, 0, 1, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 25] = b4GapPatternWeight 0 1 25 * 0 :=
      b4GapContribution_from_row 0 0 1 25 0 row_00_00_01_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_25

theorem row_00_00_01_26 : b4RowContribution (![0, 0, 1, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 1, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_27
#print axioms Paper7MomentGapNumeric.row_00_00_01_26

theorem weighted_00_00_01_26 : b4RawGapContribution ![0, 0, 1, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 26] = b4GapPatternWeight 0 1 26 * 0 :=
      b4GapContribution_from_row 0 0 1 26 0 row_00_00_01_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_26

theorem row_00_00_01_27 : b4RowContribution (![0, 0, 1, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 1, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_28
#print axioms Paper7MomentGapNumeric.row_00_00_01_27

theorem weighted_00_00_01_27 : b4RawGapContribution ![0, 0, 1, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 27] = b4GapPatternWeight 0 1 27 * 0 :=
      b4GapContribution_from_row 0 0 1 27 0 row_00_00_01_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_27

theorem row_00_00_01_28 : b4RowContribution (![0, 0, 1, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 1, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_29
#print axioms Paper7MomentGapNumeric.row_00_00_01_28

theorem weighted_00_00_01_28 : b4RawGapContribution ![0, 0, 1, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 28] = b4GapPatternWeight 0 1 28 * 0 :=
      b4GapContribution_from_row 0 0 1 28 0 row_00_00_01_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_28

theorem row_00_00_01_29 : b4RowContribution (![0, 0, 1, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 1, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_30
#print axioms Paper7MomentGapNumeric.row_00_00_01_29

theorem weighted_00_00_01_29 : b4RawGapContribution ![0, 0, 1, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 29] = b4GapPatternWeight 0 1 29 * 0 :=
      b4GapContribution_from_row 0 0 1 29 0 row_00_00_01_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_29

theorem row_00_00_01_30 : b4RowContribution (![0, 0, 1, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 1, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_31
#print axioms Paper7MomentGapNumeric.row_00_00_01_30

theorem weighted_00_00_01_30 : b4RawGapContribution ![0, 0, 1, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 30] = b4GapPatternWeight 0 1 30 * 0 :=
      b4GapContribution_from_row 0 0 1 30 0 row_00_00_01_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_30

theorem row_00_00_01_31 : b4RowContribution (![0, 0, 1, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 1, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_32
#print axioms Paper7MomentGapNumeric.row_00_00_01_31

theorem weighted_00_00_01_31 : b4RawGapContribution ![0, 0, 1, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 31] = b4GapPatternWeight 0 1 31 * 0 :=
      b4GapContribution_from_row 0 0 1 31 0 row_00_00_01_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_31

theorem row_00_00_01_32 : b4RowContribution (![0, 0, 1, 33] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨33, by decide⟩⟩ = (![0, 0, 1, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_33
#print axioms Paper7MomentGapNumeric.row_00_00_01_32

theorem weighted_00_00_01_32 : b4RawGapContribution ![0, 0, 1, 32] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 32] = b4GapPatternWeight 0 1 32 * 0 :=
      b4GapContribution_from_row 0 0 1 32 0 row_00_00_01_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_32

theorem row_00_00_01_33 : b4RowContribution (![0, 0, 1, 34] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨34, by decide⟩⟩ = (![0, 0, 1, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_34
#print axioms Paper7MomentGapNumeric.row_00_00_01_33

theorem weighted_00_00_01_33 : b4RawGapContribution ![0, 0, 1, 33] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 33] = b4GapPatternWeight 0 1 33 * 0 :=
      b4GapContribution_from_row 0 0 1 33 0 row_00_00_01_33
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_33

theorem row_00_00_01_34 : b4RowContribution (![0, 0, 1, 35] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨35, by decide⟩⟩ = (![0, 0, 1, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_35
#print axioms Paper7MomentGapNumeric.row_00_00_01_34

theorem weighted_00_00_01_34 : b4RawGapContribution ![0, 0, 1, 34] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 34] = b4GapPatternWeight 0 1 34 * 0 :=
      b4GapContribution_from_row 0 0 1 34 0 row_00_00_01_34
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_34

theorem row_00_00_01_35 : b4RowContribution (![0, 0, 1, 36] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨1, by decide⟩, ⟨36, by decide⟩⟩ = (![0, 0, 1, 36] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_01_36
#print axioms Paper7MomentGapNumeric.row_00_00_01_35

theorem weighted_00_00_01_35 : b4RawGapContribution ![0, 0, 1, 35] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 1, 35] = b4GapPatternWeight 0 1 35 * 0 :=
      b4GapContribution_from_row 0 0 1 35 0 row_00_00_01_35
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_01_35

def dvalues_00_00_01 : Fin 36 → ℕ := ![0, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 12, 24, 24, 0, 24, 0, 0, 0, 0, 0, 24, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_01

theorem dblock_00_00_01 : b4GapPatternDBlock 0 0 1 = 168 := by
  calc
    b4GapPatternDBlock 0 0 1 = ∑ d : Fin 36, dvalues_00_00_01 d := by
      apply b4GapDBlock_of_rows 0 0 1 dvalues_00_00_01
      intro d
      fin_cases d
      · exact weighted_00_00_01_00
      · exact weighted_00_00_01_01
      · exact weighted_00_00_01_02
      · exact weighted_00_00_01_03
      · exact weighted_00_00_01_04
      · exact weighted_00_00_01_05
      · exact weighted_00_00_01_06
      · exact weighted_00_00_01_07
      · exact weighted_00_00_01_08
      · exact weighted_00_00_01_09
      · exact weighted_00_00_01_10
      · exact weighted_00_00_01_11
      · exact weighted_00_00_01_12
      · exact weighted_00_00_01_13
      · exact weighted_00_00_01_14
      · exact weighted_00_00_01_15
      · exact weighted_00_00_01_16
      · exact weighted_00_00_01_17
      · exact weighted_00_00_01_18
      · exact weighted_00_00_01_19
      · exact weighted_00_00_01_20
      · exact weighted_00_00_01_21
      · exact weighted_00_00_01_22
      · exact weighted_00_00_01_23
      · exact weighted_00_00_01_24
      · exact weighted_00_00_01_25
      · exact weighted_00_00_01_26
      · exact weighted_00_00_01_27
      · exact weighted_00_00_01_28
      · exact weighted_00_00_01_29
      · exact weighted_00_00_01_30
      · exact weighted_00_00_01_31
      · exact weighted_00_00_01_32
      · exact weighted_00_00_01_33
      · exact weighted_00_00_01_34
      · exact weighted_00_00_01_35
    _ = 168 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_01

end Paper7MomentGapNumeric
