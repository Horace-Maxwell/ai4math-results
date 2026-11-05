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

theorem row_01_02_10_00 : b4RowContribution (![1, 3, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 13^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_00

theorem weighted_01_02_10_00 : b4RawGapContribution ![1, 2, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 0] = b4GapPatternWeight 2 10 0 * 0 :=
      b4GapContribution_from_row 1 2 10 0 0 row_01_02_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_00

theorem row_01_02_10_01 : b4RowContribution (![1, 3, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 14^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_01

theorem weighted_01_02_10_01 : b4RawGapContribution ![1, 2, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 1] = b4GapPatternWeight 2 10 1 * 0 :=
      b4GapContribution_from_row 1 2 10 1 0 row_01_02_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_01

theorem row_01_02_10_02 : b4RowContribution (![1, 3, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 15^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_02

theorem weighted_01_02_10_02 : b4RawGapContribution ![1, 2, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 2] = b4GapPatternWeight 2 10 2 * 0 :=
      b4GapContribution_from_row 1 2 10 2 0 row_01_02_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_02

theorem row_01_02_10_03 : b4RowContribution (![1, 3, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 16^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_03

theorem weighted_01_02_10_03 : b4RawGapContribution ![1, 2, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 3] = b4GapPatternWeight 2 10 3 * 0 :=
      b4GapContribution_from_row 1 2 10 3 0 row_01_02_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_03

theorem row_01_02_10_04 : b4RowContribution (![1, 3, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 17^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_04

theorem weighted_01_02_10_04 : b4RawGapContribution ![1, 2, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 4] = b4GapPatternWeight 2 10 4 * 0 :=
      b4GapContribution_from_row 1 2 10 4 0 row_01_02_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_04

theorem row_01_02_10_05 : b4RowContribution (![1, 3, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 503 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 18^2 = 503
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_05

theorem weighted_01_02_10_05 : b4RawGapContribution ![1, 2, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 5] = b4GapPatternWeight 2 10 5 * 0 :=
      b4GapContribution_from_row 1 2 10 5 0 row_01_02_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_05

theorem row_01_02_10_06 : b4RowContribution (![1, 3, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 540 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 19^2 = 540
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_06

theorem weighted_01_02_10_06 : b4RawGapContribution ![1, 2, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 6] = b4GapPatternWeight 2 10 6 * 0 :=
      b4GapContribution_from_row 1 2 10 6 0 row_01_02_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_06

theorem row_01_02_10_07 : b4RowContribution (![1, 3, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 13, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 13 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 13^2 + 20^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_10_07

theorem weighted_01_02_10_07 : b4RawGapContribution ![1, 2, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 10, 7] = b4GapPatternWeight 2 10 7 * 0 :=
      b4GapContribution_from_row 1 2 10 7 0 row_01_02_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_10_07

def dvalues_01_02_10 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_10

theorem dblock_01_02_10 : b4GapPatternDBlock 1 2 10 = 0 := by
  calc
    b4GapPatternDBlock 1 2 10 = ∑ d : Fin 8, dvalues_01_02_10 d := by
      apply b4GapDBlock_of_rows 1 2 10 dvalues_01_02_10
      intro d
      fin_cases d
      · exact weighted_01_02_10_00
      · exact weighted_01_02_10_01
      · exact weighted_01_02_10_02
      · exact weighted_01_02_10_03
      · exact weighted_01_02_10_04
      · exact weighted_01_02_10_05
      · exact weighted_01_02_10_06
      · exact weighted_01_02_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_10

end Paper7MomentGapNumeric
