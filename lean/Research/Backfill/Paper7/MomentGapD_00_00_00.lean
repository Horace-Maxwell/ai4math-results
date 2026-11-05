import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C00
import Research.Backfill.Paper7.MomentB4ZeroRowPrototype
import Research.Backfill.Paper7.MomentB4RepeatedRowPrototype

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

theorem weighted_00_00_00_00 : b4RawGapContribution ![0, 0, 0, 0] = 0 :=
  Paper7MomentNumericPrototype.zero_gap_contribution
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_00

theorem row_00_00_00_01 : b4RowContribution (![0, 0, 0, 1] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨1, by decide⟩⟩ = (![0, 0, 0, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_01
#print axioms Paper7MomentGapNumeric.row_00_00_00_01

theorem weighted_00_00_00_01 : b4RawGapContribution ![0, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 0 0 0 1 0 row_00_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_01

theorem row_00_00_00_02 : b4RowContribution (![0, 0, 0, 2] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨2, by decide⟩⟩ = (![0, 0, 0, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_02
#print axioms Paper7MomentGapNumeric.row_00_00_00_02

theorem weighted_00_00_00_02 : b4RawGapContribution ![0, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 0 0 0 2 0 row_00_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_02

theorem row_00_00_00_03 : b4RowContribution (![0, 0, 0, 3] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨3, by decide⟩⟩ = (![0, 0, 0, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_03
#print axioms Paper7MomentGapNumeric.row_00_00_00_03

theorem weighted_00_00_00_03 : b4RawGapContribution ![0, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 0 0 0 3 0 row_00_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_03

theorem row_00_00_00_04 : b4RowContribution (![0, 0, 0, 4] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨4, by decide⟩⟩ = (![0, 0, 0, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_04
#print axioms Paper7MomentGapNumeric.row_00_00_00_04

theorem weighted_00_00_00_04 : b4RawGapContribution ![0, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 0 0 0 4 0 row_00_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_04

theorem row_00_00_00_05 : b4RowContribution (![0, 0, 0, 5] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 0, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_05
#print axioms Paper7MomentGapNumeric.row_00_00_00_05

theorem weighted_00_00_00_05 : b4RawGapContribution ![0, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 0 0 0 5 0 row_00_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_05

theorem row_00_00_00_06 : b4RowContribution (![0, 0, 0, 6] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 0, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_06
#print axioms Paper7MomentGapNumeric.row_00_00_00_06

theorem weighted_00_00_00_06 : b4RawGapContribution ![0, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 0 0 0 6 0 row_00_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_06

theorem weighted_00_00_00_07 : b4RawGapContribution ![0, 0, 0, 7] = 4 :=
  Paper7MomentNumericPrototype.repeated_gap_contribution
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_07

theorem row_00_00_00_08 : b4RowContribution (![0, 0, 0, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 0, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_08
#print axioms Paper7MomentGapNumeric.row_00_00_00_08

theorem weighted_00_00_00_08 : b4RawGapContribution ![0, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 0 0 0 8 0 row_00_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_08

theorem row_00_00_00_09 : b4RowContribution (![0, 0, 0, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 0, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_09
#print axioms Paper7MomentGapNumeric.row_00_00_00_09

theorem weighted_00_00_00_09 : b4RawGapContribution ![0, 0, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 0 :=
      b4GapContribution_from_row 0 0 0 9 0 row_00_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_09

theorem row_00_00_00_10 : b4RowContribution (![0, 0, 0, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 0, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_10
#print axioms Paper7MomentGapNumeric.row_00_00_00_10

theorem weighted_00_00_00_10 : b4RawGapContribution ![0, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 0 0 0 10 0 row_00_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_10

theorem row_00_00_00_11 : b4RowContribution (![0, 0, 0, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 0, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_11
#print axioms Paper7MomentGapNumeric.row_00_00_00_11

theorem weighted_00_00_00_11 : b4RawGapContribution ![0, 0, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 0 :=
      b4GapContribution_from_row 0 0 0 11 0 row_00_00_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_11

theorem row_00_00_00_12 : b4RowContribution (![0, 0, 0, 12] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 0, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_12
#print axioms Paper7MomentGapNumeric.row_00_00_00_12

theorem weighted_00_00_00_12 : b4RawGapContribution ![0, 0, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 0 :=
      b4GapContribution_from_row 0 0 0 12 0 row_00_00_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_12

theorem row_00_00_00_13 : b4RowContribution (![0, 0, 0, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 0, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_13
#print axioms Paper7MomentGapNumeric.row_00_00_00_13

theorem weighted_00_00_00_13 : b4RawGapContribution ![0, 0, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 0 :=
      b4GapContribution_from_row 0 0 0 13 0 row_00_00_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_13

theorem row_00_00_00_14 : b4RowContribution (![0, 0, 0, 14] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 0, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_14
#print axioms Paper7MomentGapNumeric.row_00_00_00_14

theorem weighted_00_00_00_14 : b4RawGapContribution ![0, 0, 0, 14] = 4 := by
  calc
    b4RawGapContribution ![0, 0, 0, 14] = b4GapPatternWeight 0 0 14 * 1 :=
      b4GapContribution_from_row 0 0 0 14 1 row_00_00_00_14
    _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_14

theorem row_00_00_00_15 : b4RowContribution (![0, 0, 0, 15] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 0, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_15
#print axioms Paper7MomentGapNumeric.row_00_00_00_15

theorem weighted_00_00_00_15 : b4RawGapContribution ![0, 0, 0, 15] = 4 := by
  calc
    b4RawGapContribution ![0, 0, 0, 15] = b4GapPatternWeight 0 0 15 * 1 :=
      b4GapContribution_from_row 0 0 0 15 1 row_00_00_00_15
    _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_15

theorem row_00_00_00_16 : b4RowContribution (![0, 0, 0, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 0, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_16
#print axioms Paper7MomentGapNumeric.row_00_00_00_16

theorem weighted_00_00_00_16 : b4RawGapContribution ![0, 0, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 16] = b4GapPatternWeight 0 0 16 * 0 :=
      b4GapContribution_from_row 0 0 0 16 0 row_00_00_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_16

theorem row_00_00_00_17 : b4RowContribution (![0, 0, 0, 17] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 0, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_17
#print axioms Paper7MomentGapNumeric.row_00_00_00_17

theorem weighted_00_00_00_17 : b4RawGapContribution ![0, 0, 0, 17] = 4 := by
  calc
    b4RawGapContribution ![0, 0, 0, 17] = b4GapPatternWeight 0 0 17 * 1 :=
      b4GapContribution_from_row 0 0 0 17 1 row_00_00_00_17
    _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_17

theorem row_00_00_00_18 : b4RowContribution (![0, 0, 0, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 0, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_18
#print axioms Paper7MomentGapNumeric.row_00_00_00_18

theorem weighted_00_00_00_18 : b4RawGapContribution ![0, 0, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 18] = b4GapPatternWeight 0 0 18 * 0 :=
      b4GapContribution_from_row 0 0 0 18 0 row_00_00_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_18

theorem row_00_00_00_19 : b4RowContribution (![0, 0, 0, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 0, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_19
#print axioms Paper7MomentGapNumeric.row_00_00_00_19

theorem weighted_00_00_00_19 : b4RawGapContribution ![0, 0, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 19] = b4GapPatternWeight 0 0 19 * 0 :=
      b4GapContribution_from_row 0 0 0 19 0 row_00_00_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_19

theorem row_00_00_00_20 : b4RowContribution (![0, 0, 0, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 0, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_20
#print axioms Paper7MomentGapNumeric.row_00_00_00_20

theorem weighted_00_00_00_20 : b4RawGapContribution ![0, 0, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 20] = b4GapPatternWeight 0 0 20 * 0 :=
      b4GapContribution_from_row 0 0 0 20 0 row_00_00_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_20

theorem row_00_00_00_21 : b4RowContribution (![0, 0, 0, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 0, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_21
#print axioms Paper7MomentGapNumeric.row_00_00_00_21

theorem weighted_00_00_00_21 : b4RawGapContribution ![0, 0, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 21] = b4GapPatternWeight 0 0 21 * 0 :=
      b4GapContribution_from_row 0 0 0 21 0 row_00_00_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_21

theorem row_00_00_00_22 : b4RowContribution (![0, 0, 0, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 0, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_22
#print axioms Paper7MomentGapNumeric.row_00_00_00_22

theorem weighted_00_00_00_22 : b4RawGapContribution ![0, 0, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 22] = b4GapPatternWeight 0 0 22 * 0 :=
      b4GapContribution_from_row 0 0 0 22 0 row_00_00_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_22

theorem row_00_00_00_23 : b4RowContribution (![0, 0, 0, 23] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 0, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_23
#print axioms Paper7MomentGapNumeric.row_00_00_00_23

theorem weighted_00_00_00_23 : b4RawGapContribution ![0, 0, 0, 23] = 4 := by
  calc
    b4RawGapContribution ![0, 0, 0, 23] = b4GapPatternWeight 0 0 23 * 1 :=
      b4GapContribution_from_row 0 0 0 23 1 row_00_00_00_23
    _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_23

theorem row_00_00_00_24 : b4RowContribution (![0, 0, 0, 24] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 0, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_24
#print axioms Paper7MomentGapNumeric.row_00_00_00_24

theorem weighted_00_00_00_24 : b4RawGapContribution ![0, 0, 0, 24] = 8 := by
  calc
    b4RawGapContribution ![0, 0, 0, 24] = b4GapPatternWeight 0 0 24 * 2 :=
      b4GapContribution_from_row 0 0 0 24 2 row_00_00_00_24
    _ = 8 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_24

theorem row_00_00_00_25 : b4RowContribution (![0, 0, 0, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 0, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_25
#print axioms Paper7MomentGapNumeric.row_00_00_00_25

theorem weighted_00_00_00_25 : b4RawGapContribution ![0, 0, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 25] = b4GapPatternWeight 0 0 25 * 0 :=
      b4GapContribution_from_row 0 0 0 25 0 row_00_00_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_25

theorem row_00_00_00_26 : b4RowContribution (![0, 0, 0, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 0, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_26
#print axioms Paper7MomentGapNumeric.row_00_00_00_26

theorem weighted_00_00_00_26 : b4RawGapContribution ![0, 0, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 26] = b4GapPatternWeight 0 0 26 * 0 :=
      b4GapContribution_from_row 0 0 0 26 0 row_00_00_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_26

theorem row_00_00_00_27 : b4RowContribution (![0, 0, 0, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 0, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_27
#print axioms Paper7MomentGapNumeric.row_00_00_00_27

theorem weighted_00_00_00_27 : b4RawGapContribution ![0, 0, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 27] = b4GapPatternWeight 0 0 27 * 0 :=
      b4GapContribution_from_row 0 0 0 27 0 row_00_00_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_27

theorem row_00_00_00_28 : b4RowContribution (![0, 0, 0, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 0, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_28
#print axioms Paper7MomentGapNumeric.row_00_00_00_28

theorem weighted_00_00_00_28 : b4RawGapContribution ![0, 0, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 28] = b4GapPatternWeight 0 0 28 * 0 :=
      b4GapContribution_from_row 0 0 0 28 0 row_00_00_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_28

theorem row_00_00_00_29 : b4RowContribution (![0, 0, 0, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 0, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_29
#print axioms Paper7MomentGapNumeric.row_00_00_00_29

theorem weighted_00_00_00_29 : b4RawGapContribution ![0, 0, 0, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 29] = b4GapPatternWeight 0 0 29 * 0 :=
      b4GapContribution_from_row 0 0 0 29 0 row_00_00_00_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_29

theorem row_00_00_00_30 : b4RowContribution (![0, 0, 0, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 0, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_30
#print axioms Paper7MomentGapNumeric.row_00_00_00_30

theorem weighted_00_00_00_30 : b4RawGapContribution ![0, 0, 0, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 30] = b4GapPatternWeight 0 0 30 * 0 :=
      b4GapContribution_from_row 0 0 0 30 0 row_00_00_00_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_30

theorem row_00_00_00_31 : b4RowContribution (![0, 0, 0, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 0, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_31
#print axioms Paper7MomentGapNumeric.row_00_00_00_31

theorem weighted_00_00_00_31 : b4RawGapContribution ![0, 0, 0, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 31] = b4GapPatternWeight 0 0 31 * 0 :=
      b4GapContribution_from_row 0 0 0 31 0 row_00_00_00_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_31

theorem row_00_00_00_32 : b4RowContribution (![0, 0, 0, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 0, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_32
#print axioms Paper7MomentGapNumeric.row_00_00_00_32

theorem weighted_00_00_00_32 : b4RawGapContribution ![0, 0, 0, 32] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 32] = b4GapPatternWeight 0 0 32 * 0 :=
      b4GapContribution_from_row 0 0 0 32 0 row_00_00_00_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_32

theorem row_00_00_00_33 : b4RowContribution (![0, 0, 0, 33] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨33, by decide⟩⟩ = (![0, 0, 0, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_33
#print axioms Paper7MomentGapNumeric.row_00_00_00_33

theorem weighted_00_00_00_33 : b4RawGapContribution ![0, 0, 0, 33] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 33] = b4GapPatternWeight 0 0 33 * 0 :=
      b4GapContribution_from_row 0 0 0 33 0 row_00_00_00_33
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_33

theorem row_00_00_00_34 : b4RowContribution (![0, 0, 0, 34] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨34, by decide⟩⟩ = (![0, 0, 0, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_34
#print axioms Paper7MomentGapNumeric.row_00_00_00_34

theorem weighted_00_00_00_34 : b4RawGapContribution ![0, 0, 0, 34] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 34] = b4GapPatternWeight 0 0 34 * 0 :=
      b4GapContribution_from_row 0 0 0 34 0 row_00_00_00_34
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_34

theorem row_00_00_00_35 : b4RowContribution (![0, 0, 0, 35] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨35, by decide⟩⟩ = (![0, 0, 0, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_35
#print axioms Paper7MomentGapNumeric.row_00_00_00_35

theorem weighted_00_00_00_35 : b4RawGapContribution ![0, 0, 0, 35] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 35] = b4GapPatternWeight 0 0 35 * 0 :=
      b4GapContribution_from_row 0 0 0 35 0 row_00_00_00_35
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_35

theorem row_00_00_00_36 : b4RowContribution (![0, 0, 0, 36] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨36, by decide⟩⟩ = (![0, 0, 0, 36] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_36
#print axioms Paper7MomentGapNumeric.row_00_00_00_36

theorem weighted_00_00_00_36 : b4RawGapContribution ![0, 0, 0, 36] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 36] = b4GapPatternWeight 0 0 36 * 0 :=
      b4GapContribution_from_row 0 0 0 36 0 row_00_00_00_36
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_36

theorem row_00_00_00_37 : b4RowContribution (![0, 0, 0, 37] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨37, by decide⟩⟩ = (![0, 0, 0, 37] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_37
#print axioms Paper7MomentGapNumeric.row_00_00_00_37

theorem weighted_00_00_00_37 : b4RawGapContribution ![0, 0, 0, 37] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 37] = b4GapPatternWeight 0 0 37 * 0 :=
      b4GapContribution_from_row 0 0 0 37 0 row_00_00_00_37
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_00_37

def dvalues_00_00_00 : Fin 38 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 4, 0, 4, 0, 0, 0, 0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_00

theorem dblock_00_00_00 : b4GapPatternDBlock 0 0 0 = 28 := by
  calc
    b4GapPatternDBlock 0 0 0 = ∑ d : Fin 38, dvalues_00_00_00 d := by
      apply b4GapDBlock_of_rows 0 0 0 dvalues_00_00_00
      intro d
      fin_cases d
      · exact weighted_00_00_00_00
      · exact weighted_00_00_00_01
      · exact weighted_00_00_00_02
      · exact weighted_00_00_00_03
      · exact weighted_00_00_00_04
      · exact weighted_00_00_00_05
      · exact weighted_00_00_00_06
      · exact weighted_00_00_00_07
      · exact weighted_00_00_00_08
      · exact weighted_00_00_00_09
      · exact weighted_00_00_00_10
      · exact weighted_00_00_00_11
      · exact weighted_00_00_00_12
      · exact weighted_00_00_00_13
      · exact weighted_00_00_00_14
      · exact weighted_00_00_00_15
      · exact weighted_00_00_00_16
      · exact weighted_00_00_00_17
      · exact weighted_00_00_00_18
      · exact weighted_00_00_00_19
      · exact weighted_00_00_00_20
      · exact weighted_00_00_00_21
      · exact weighted_00_00_00_22
      · exact weighted_00_00_00_23
      · exact weighted_00_00_00_24
      · exact weighted_00_00_00_25
      · exact weighted_00_00_00_26
      · exact weighted_00_00_00_27
      · exact weighted_00_00_00_28
      · exact weighted_00_00_00_29
      · exact weighted_00_00_00_30
      · exact weighted_00_00_00_31
      · exact weighted_00_00_00_32
      · exact weighted_00_00_00_33
      · exact weighted_00_00_00_34
      · exact weighted_00_00_00_35
      · exact weighted_00_00_00_36
      · exact weighted_00_00_00_37
    _ = 28 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_00

end Paper7MomentGapNumeric
