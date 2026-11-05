import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate

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

theorem row_01_06_00_00 : b4RowContribution (![1, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 7] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 7 = 22
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_00

theorem weighted_01_06_00_00 : b4RawGapContribution ![1, 6, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 0] = b4GapPatternWeight 6 0 0 * 0 :=
      b4GapContribution_from_row 1 6 0 0 0 row_01_06_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_00

theorem row_01_06_00_01 : b4RowContribution (![1, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 8 = 23
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 163
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_01

theorem weighted_01_06_00_01 : b4RawGapContribution ![1, 6, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 1] = b4GapPatternWeight 6 0 1 * 0 :=
      b4GapContribution_from_row 1 6 0 1 0 row_01_06_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_01

theorem row_01_06_00_02 : b4RowContribution (![1, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 9 = 24
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_02

theorem weighted_01_06_00_02 : b4RawGapContribution ![1, 6, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 2] = b4GapPatternWeight 6 0 2 * 0 :=
      b4GapContribution_from_row 1 6 0 2 0 row_01_06_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_02

theorem row_01_06_00_03 : b4RowContribution (![1, 7, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 10 = 25
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 199 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 199
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_03

theorem weighted_01_06_00_03 : b4RawGapContribution ![1, 6, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 3] = b4GapPatternWeight 6 0 3 * 0 :=
      b4GapContribution_from_row 1 6 0 3 0 row_01_06_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_03

theorem row_01_06_00_04 : b4RowContribution (![1, 7, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 11 = 26
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 220
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_04

theorem weighted_01_06_00_04 : b4RawGapContribution ![1, 6, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 4] = b4GapPatternWeight 6 0 4 * 0 :=
      b4GapContribution_from_row 1 6 0 4 0 row_01_06_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_04

theorem row_01_06_00_05 : b4RowContribution (![1, 7, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 12 = 27
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_05

theorem weighted_01_06_00_05 : b4RawGapContribution ![1, 6, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 5] = b4GapPatternWeight 6 0 5 * 0 :=
      b4GapContribution_from_row 1 6 0 5 0 row_01_06_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_05

theorem row_01_06_00_06 : b4RowContribution (![1, 7, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 13 = 28
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_06

theorem weighted_01_06_00_06 : b4RawGapContribution ![1, 6, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 6] = b4GapPatternWeight 6 0 6 * 0 :=
      b4GapContribution_from_row 1 6 0 6 0 row_01_06_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_06

theorem row_01_06_00_07 : b4RowContribution (![1, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_07

theorem weighted_01_06_00_07 : b4RawGapContribution ![1, 6, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 7] = b4GapPatternWeight 6 0 7 * 0 :=
      b4GapContribution_from_row 1 6 0 7 0 row_01_06_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_07

theorem row_01_06_00_08 : b4RowContribution (![1, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_08

theorem weighted_01_06_00_08 : b4RawGapContribution ![1, 6, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 8] = b4GapPatternWeight 6 0 8 * 0 :=
      b4GapContribution_from_row 1 6 0 8 0 row_01_06_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_08

theorem row_01_06_00_09 : b4RowContribution (![1, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_09

theorem weighted_01_06_00_09 : b4RawGapContribution ![1, 6, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 9] = b4GapPatternWeight 6 0 9 * 0 :=
      b4GapContribution_from_row 1 6 0 9 0 row_01_06_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_09

theorem row_01_06_00_10 : b4RowContribution (![1, 7, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 17^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_10

theorem weighted_01_06_00_10 : b4RawGapContribution ![1, 6, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 10] = b4GapPatternWeight 6 0 10 * 0 :=
      b4GapContribution_from_row 1 6 0 10 0 row_01_06_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_10

theorem row_01_06_00_11 : b4RowContribution (![1, 7, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 18^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_11

theorem weighted_01_06_00_11 : b4RawGapContribution ![1, 6, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 11] = b4GapPatternWeight 6 0 11 * 0 :=
      b4GapContribution_from_row 1 6 0 11 0 row_01_06_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_11

theorem row_01_06_00_12 : b4RowContribution (![1, 7, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 19^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_12

theorem weighted_01_06_00_12 : b4RawGapContribution ![1, 6, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 12] = b4GapPatternWeight 6 0 12 * 0 :=
      b4GapContribution_from_row 1 6 0 12 0 row_01_06_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_12

theorem row_01_06_00_13 : b4RowContribution (![1, 7, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 499 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 20^2 = 499
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_13

theorem weighted_01_06_00_13 : b4RawGapContribution ![1, 6, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 13] = b4GapPatternWeight 6 0 13 * 0 :=
      b4GapContribution_from_row 1 6 0 13 0 row_01_06_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_13

theorem row_01_06_00_14 : b4RowContribution (![1, 7, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 540 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 21^2 = 540
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_14

theorem weighted_01_06_00_14 : b4RawGapContribution ![1, 6, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 14] = b4GapPatternWeight 6 0 14 * 0 :=
      b4GapContribution_from_row 1 6 0 14 0 row_01_06_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_14

theorem row_01_06_00_15 : b4RowContribution (![1, 7, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 7, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 7 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 583 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 7^2 + 22^2 = 583
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_00_15

theorem weighted_01_06_00_15 : b4RawGapContribution ![1, 6, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 0, 15] = b4GapPatternWeight 6 0 15 * 0 :=
      b4GapContribution_from_row 1 6 0 15 0 row_01_06_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_00_15

def dvalues_01_06_00 : Fin 16 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_00

theorem dblock_01_06_00 : b4GapPatternDBlock 1 6 0 = 0 := by
  calc
    b4GapPatternDBlock 1 6 0 = ∑ d : Fin 16, dvalues_01_06_00 d := by
      apply b4GapDBlock_of_rows 1 6 0 dvalues_01_06_00
      intro d
      fin_cases d
      · exact weighted_01_06_00_00
      · exact weighted_01_06_00_01
      · exact weighted_01_06_00_02
      · exact weighted_01_06_00_03
      · exact weighted_01_06_00_04
      · exact weighted_01_06_00_05
      · exact weighted_01_06_00_06
      · exact weighted_01_06_00_07
      · exact weighted_01_06_00_08
      · exact weighted_01_06_00_09
      · exact weighted_01_06_00_10
      · exact weighted_01_06_00_11
      · exact weighted_01_06_00_12
      · exact weighted_01_06_00_13
      · exact weighted_01_06_00_14
      · exact weighted_01_06_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_00

end Paper7MomentGapNumeric
