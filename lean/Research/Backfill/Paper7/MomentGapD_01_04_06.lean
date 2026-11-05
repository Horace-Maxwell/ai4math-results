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

theorem row_01_04_06_00 : b4RowContribution (![1, 5, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 11 = 28
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 11^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_00

theorem weighted_01_04_06_00 : b4RawGapContribution ![1, 4, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 0] = b4GapPatternWeight 4 6 0 * 0 :=
      b4GapContribution_from_row 1 4 6 0 0 row_01_04_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_00

theorem row_01_04_06_01 : b4RowContribution (![1, 5, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 12 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 12^2 = 291
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_01

theorem weighted_01_04_06_01 : b4RawGapContribution ![1, 4, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 1] = b4GapPatternWeight 4 6 1 * 0 :=
      b4GapContribution_from_row 1 4 6 1 0 row_01_04_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_01

theorem row_01_04_06_02 : b4RowContribution (![1, 5, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 13^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_02

theorem weighted_01_04_06_02 : b4RawGapContribution ![1, 4, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 2] = b4GapPatternWeight 4 6 2 * 0 :=
      b4GapContribution_from_row 1 4 6 2 0 row_01_04_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_02

theorem row_01_04_06_03 : b4RowContribution (![1, 5, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 14^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_03

theorem weighted_01_04_06_03 : b4RawGapContribution ![1, 4, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 3] = b4GapPatternWeight 4 6 3 * 0 :=
      b4GapContribution_from_row 1 4 6 3 0 row_01_04_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_03

theorem row_01_04_06_04 : b4RowContribution (![1, 5, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 15^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_04

theorem weighted_01_04_06_04 : b4RawGapContribution ![1, 4, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 4] = b4GapPatternWeight 4 6 4 * 0 :=
      b4GapContribution_from_row 1 4 6 4 0 row_01_04_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_04

theorem row_01_04_06_05 : b4RowContribution (![1, 5, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 16^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_05

theorem weighted_01_04_06_05 : b4RawGapContribution ![1, 4, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 5] = b4GapPatternWeight 4 6 5 * 0 :=
      b4GapContribution_from_row 1 4 6 5 0 row_01_04_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_05

theorem row_01_04_06_06 : b4RowContribution (![1, 5, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 436 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 17^2 = 436
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_06

theorem weighted_01_04_06_06 : b4RawGapContribution ![1, 4, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 6] = b4GapPatternWeight 4 6 6 * 0 :=
      b4GapContribution_from_row 1 4 6 6 0 row_01_04_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_06

theorem row_01_04_06_07 : b4RowContribution (![1, 5, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 18^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_07

theorem weighted_01_04_06_07 : b4RawGapContribution ![1, 4, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 7] = b4GapPatternWeight 4 6 7 * 0 :=
      b4GapContribution_from_row 1 4 6 7 0 row_01_04_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_07

theorem row_01_04_06_08 : b4RowContribution (![1, 5, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 508 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 19^2 = 508
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_08

theorem weighted_01_04_06_08 : b4RawGapContribution ![1, 4, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 8] = b4GapPatternWeight 4 6 8 * 0 :=
      b4GapContribution_from_row 1 4 6 8 0 row_01_04_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_08

theorem row_01_04_06_09 : b4RowContribution (![1, 5, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 11, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 11 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 11^2 + 20^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_06_09

theorem weighted_01_04_06_09 : b4RawGapContribution ![1, 4, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 6, 9] = b4GapPatternWeight 4 6 9 * 0 :=
      b4GapContribution_from_row 1 4 6 9 0 row_01_04_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_06_09

def dvalues_01_04_06 : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_06

theorem dblock_01_04_06 : b4GapPatternDBlock 1 4 6 = 0 := by
  calc
    b4GapPatternDBlock 1 4 6 = ∑ d : Fin 10, dvalues_01_04_06 d := by
      apply b4GapDBlock_of_rows 1 4 6 dvalues_01_04_06
      intro d
      fin_cases d
      · exact weighted_01_04_06_00
      · exact weighted_01_04_06_01
      · exact weighted_01_04_06_02
      · exact weighted_01_04_06_03
      · exact weighted_01_04_06_04
      · exact weighted_01_04_06_05
      · exact weighted_01_04_06_06
      · exact weighted_01_04_06_07
      · exact weighted_01_04_06_08
      · exact weighted_01_04_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_06

end Paper7MomentGapNumeric
