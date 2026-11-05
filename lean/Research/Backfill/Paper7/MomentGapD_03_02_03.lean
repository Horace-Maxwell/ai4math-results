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

theorem row_03_02_03_00 : b4RowContribution (![3, 5, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 8 = 24
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 8^2 = 162
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_00

theorem weighted_03_02_03_00 : b4RawGapContribution ![3, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 3 2 3 0 0 row_03_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_00

theorem row_03_02_03_01 : b4RowContribution (![3, 5, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 9 = 25
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 179 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 9^2 = 179
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_01

theorem weighted_03_02_03_01 : b4RawGapContribution ![3, 2, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 0 :=
      b4GapContribution_from_row 3 2 3 1 0 row_03_02_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_01

theorem row_03_02_03_02 : b4RowContribution (![3, 5, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 10 = 26
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 10^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_02

theorem weighted_03_02_03_02 : b4RawGapContribution ![3, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 3 2 3 2 0 row_03_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_02

theorem row_03_02_03_03 : b4RowContribution (![3, 5, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 11 = 27
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 11^2 = 219
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_03

theorem weighted_03_02_03_03 : b4RawGapContribution ![3, 2, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 0 :=
      b4GapContribution_from_row 3 2 3 3 0 row_03_02_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_03

theorem row_03_02_03_04 : b4RowContribution (![3, 5, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 12 = 28
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 12^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_04

theorem weighted_03_02_03_04 : b4RawGapContribution ![3, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 3 2 3 4 0 row_03_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_04

theorem row_03_02_03_05 : b4RowContribution (![3, 5, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 13 = 29
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 13^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_05

theorem weighted_03_02_03_05 : b4RawGapContribution ![3, 2, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 0 :=
      b4GapContribution_from_row 3 2 3 5 0 row_03_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_05

theorem row_03_02_03_06 : b4RowContribution (![3, 5, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 14 = 30
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 14^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_06

theorem weighted_03_02_03_06 : b4RawGapContribution ![3, 2, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 6] = b4GapPatternWeight 2 3 6 * 0 :=
      b4GapContribution_from_row 3 2 3 6 0 row_03_02_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_06

theorem row_03_02_03_07 : b4RowContribution (![3, 5, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 15 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 15^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_07

theorem weighted_03_02_03_07 : b4RawGapContribution ![3, 2, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 7] = b4GapPatternWeight 2 3 7 * 0 :=
      b4GapContribution_from_row 3 2 3 7 0 row_03_02_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_07

theorem row_03_02_03_08 : b4RowContribution (![3, 5, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 16 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 16^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_08

theorem weighted_03_02_03_08 : b4RawGapContribution ![3, 2, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 8] = b4GapPatternWeight 2 3 8 * 0 :=
      b4GapContribution_from_row 3 2 3 8 0 row_03_02_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_08

theorem row_03_02_03_09 : b4RowContribution (![3, 5, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 17 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 17^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_09

theorem weighted_03_02_03_09 : b4RawGapContribution ![3, 2, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 9] = b4GapPatternWeight 2 3 9 * 0 :=
      b4GapContribution_from_row 3 2 3 9 0 row_03_02_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_09

theorem row_03_02_03_10 : b4RowContribution (![3, 5, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 18 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 18^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_10

theorem weighted_03_02_03_10 : b4RawGapContribution ![3, 2, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 10] = b4GapPatternWeight 2 3 10 * 0 :=
      b4GapContribution_from_row 3 2 3 10 0 row_03_02_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_10

theorem row_03_02_03_11 : b4RowContribution (![3, 5, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 19 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 19^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_11

theorem weighted_03_02_03_11 : b4RawGapContribution ![3, 2, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 11] = b4GapPatternWeight 2 3 11 * 0 :=
      b4GapContribution_from_row 3 2 3 11 0 row_03_02_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_11

theorem row_03_02_03_12 : b4RowContribution (![3, 5, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 20 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 20^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_12

theorem weighted_03_02_03_12 : b4RawGapContribution ![3, 2, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 12] = b4GapPatternWeight 2 3 12 * 0 :=
      b4GapContribution_from_row 3 2 3 12 0 row_03_02_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_12

theorem row_03_02_03_13 : b4RowContribution (![3, 5, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 8, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 8 + 21 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 539 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 8^2 + 21^2 = 539
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_03_13

theorem weighted_03_02_03_13 : b4RawGapContribution ![3, 2, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 3, 13] = b4GapPatternWeight 2 3 13 * 0 :=
      b4GapContribution_from_row 3 2 3 13 0 row_03_02_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_03_13

def dvalues_03_02_03 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_03

theorem dblock_03_02_03 : b4GapPatternDBlock 3 2 3 = 0 := by
  calc
    b4GapPatternDBlock 3 2 3 = ∑ d : Fin 14, dvalues_03_02_03 d := by
      apply b4GapDBlock_of_rows 3 2 3 dvalues_03_02_03
      intro d
      fin_cases d
      · exact weighted_03_02_03_00
      · exact weighted_03_02_03_01
      · exact weighted_03_02_03_02
      · exact weighted_03_02_03_03
      · exact weighted_03_02_03_04
      · exact weighted_03_02_03_05
      · exact weighted_03_02_03_06
      · exact weighted_03_02_03_07
      · exact weighted_03_02_03_08
      · exact weighted_03_02_03_09
      · exact weighted_03_02_03_10
      · exact weighted_03_02_03_11
      · exact weighted_03_02_03_12
      · exact weighted_03_02_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_03

end Paper7MomentGapNumeric
