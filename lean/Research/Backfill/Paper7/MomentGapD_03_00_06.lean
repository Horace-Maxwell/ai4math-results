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

theorem row_03_00_06_00 : b4RowContribution (![3, 3, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 9 = 24
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 9^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_00

theorem weighted_03_00_06_00 : b4RawGapContribution ![3, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 3 0 6 0 0 row_03_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_00

theorem row_03_00_06_01 : b4RowContribution (![3, 3, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 10 = 25
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 199 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 10^2 = 199
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_01

theorem weighted_03_00_06_01 : b4RawGapContribution ![3, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 3 0 6 1 0 row_03_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_01

theorem row_03_00_06_02 : b4RowContribution (![3, 3, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 11 = 26
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 11^2 = 220
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_02

theorem weighted_03_00_06_02 : b4RawGapContribution ![3, 0, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 0 :=
      b4GapContribution_from_row 3 0 6 2 0 row_03_00_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_02

theorem row_03_00_06_03 : b4RowContribution (![3, 3, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 12 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 12^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_03

theorem weighted_03_00_06_03 : b4RawGapContribution ![3, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 3 0 6 3 0 row_03_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_03

theorem row_03_00_06_04 : b4RowContribution (![3, 3, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 13 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 13^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_04

theorem weighted_03_00_06_04 : b4RawGapContribution ![3, 0, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 0 :=
      b4GapContribution_from_row 3 0 6 4 0 row_03_00_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_04

theorem row_03_00_06_05 : b4RowContribution (![3, 3, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 14 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 14^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_05

theorem weighted_03_00_06_05 : b4RawGapContribution ![3, 0, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 0 :=
      b4GapContribution_from_row 3 0 6 5 0 row_03_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_05

theorem row_03_00_06_06 : b4RowContribution (![3, 3, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 15 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 15^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_06

theorem weighted_03_00_06_06 : b4RawGapContribution ![3, 0, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 6] = b4GapPatternWeight 0 6 6 * 0 :=
      b4GapContribution_from_row 3 0 6 6 0 row_03_00_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_06

theorem row_03_00_06_07 : b4RowContribution (![3, 3, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 16 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 16^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_07

theorem weighted_03_00_06_07 : b4RawGapContribution ![3, 0, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 7] = b4GapPatternWeight 0 6 7 * 0 :=
      b4GapContribution_from_row 3 0 6 7 0 row_03_00_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_07

theorem row_03_00_06_08 : b4RowContribution (![3, 3, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 17 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 17^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_08

theorem weighted_03_00_06_08 : b4RawGapContribution ![3, 0, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 8] = b4GapPatternWeight 0 6 8 * 0 :=
      b4GapContribution_from_row 3 0 6 8 0 row_03_00_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_08

theorem row_03_00_06_09 : b4RowContribution (![3, 3, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 18 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 18^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_09

theorem weighted_03_00_06_09 : b4RawGapContribution ![3, 0, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 9] = b4GapPatternWeight 0 6 9 * 0 :=
      b4GapContribution_from_row 3 0 6 9 0 row_03_00_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_09

theorem row_03_00_06_10 : b4RowContribution (![3, 3, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 19 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 19^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_10

theorem weighted_03_00_06_10 : b4RawGapContribution ![3, 0, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 10] = b4GapPatternWeight 0 6 10 * 0 :=
      b4GapContribution_from_row 3 0 6 10 0 row_03_00_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_10

theorem row_03_00_06_11 : b4RowContribution (![3, 3, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 20 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 499 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 20^2 = 499
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_11

theorem weighted_03_00_06_11 : b4RawGapContribution ![3, 0, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 11] = b4GapPatternWeight 0 6 11 * 0 :=
      b4GapContribution_from_row 3 0 6 11 0 row_03_00_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_11

theorem row_03_00_06_12 : b4RowContribution (![3, 3, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 21 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 540 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 21^2 = 540
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_12

theorem weighted_03_00_06_12 : b4RawGapContribution ![3, 0, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 12] = b4GapPatternWeight 0 6 12 * 0 :=
      b4GapContribution_from_row 3 0 6 12 0 row_03_00_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_12

theorem row_03_00_06_13 : b4RowContribution (![3, 3, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 9, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 9 + 22 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 583 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 9^2 + 22^2 = 583
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_06_13

theorem weighted_03_00_06_13 : b4RawGapContribution ![3, 0, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 6, 13] = b4GapPatternWeight 0 6 13 * 0 :=
      b4GapContribution_from_row 3 0 6 13 0 row_03_00_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_06_13

def dvalues_03_00_06 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_06

theorem dblock_03_00_06 : b4GapPatternDBlock 3 0 6 = 0 := by
  calc
    b4GapPatternDBlock 3 0 6 = ∑ d : Fin 14, dvalues_03_00_06 d := by
      apply b4GapDBlock_of_rows 3 0 6 dvalues_03_00_06
      intro d
      fin_cases d
      · exact weighted_03_00_06_00
      · exact weighted_03_00_06_01
      · exact weighted_03_00_06_02
      · exact weighted_03_00_06_03
      · exact weighted_03_00_06_04
      · exact weighted_03_00_06_05
      · exact weighted_03_00_06_06
      · exact weighted_03_00_06_07
      · exact weighted_03_00_06_08
      · exact weighted_03_00_06_09
      · exact weighted_03_00_06_10
      · exact weighted_03_00_06_11
      · exact weighted_03_00_06_12
      · exact weighted_03_00_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_06

end Paper7MomentGapNumeric
