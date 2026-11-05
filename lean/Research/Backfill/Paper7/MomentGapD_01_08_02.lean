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

theorem row_01_08_02_00 : b4RowContribution (![1, 9, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 11 = 32
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 11^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_00

theorem weighted_01_08_02_00 : b4RawGapContribution ![1, 8, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 0] = b4GapPatternWeight 8 2 0 * 0 :=
      b4GapContribution_from_row 1 8 2 0 0 row_01_08_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_00

theorem row_01_08_02_01 : b4RowContribution (![1, 9, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 12 = 33
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 12^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_01

theorem weighted_01_08_02_01 : b4RawGapContribution ![1, 8, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 1] = b4GapPatternWeight 8 2 1 * 0 :=
      b4GapContribution_from_row 1 8 2 1 0 row_01_08_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_01

theorem row_01_08_02_02 : b4RowContribution (![1, 9, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 13 = 34
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 13^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_02

theorem weighted_01_08_02_02 : b4RawGapContribution ![1, 8, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 2] = b4GapPatternWeight 8 2 2 * 0 :=
      b4GapContribution_from_row 1 8 2 2 0 row_01_08_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_02

theorem row_01_08_02_03 : b4RowContribution (![1, 9, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 14 = 35
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 14^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_03

theorem weighted_01_08_02_03 : b4RawGapContribution ![1, 8, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 3] = b4GapPatternWeight 8 2 3 * 0 :=
      b4GapContribution_from_row 1 8 2 3 0 row_01_08_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_03

theorem row_01_08_02_04 : b4RowContribution (![1, 9, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 15 = 36
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 15^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_04

theorem weighted_01_08_02_04 : b4RawGapContribution ![1, 8, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 4] = b4GapPatternWeight 8 2 4 * 0 :=
      b4GapContribution_from_row 1 8 2 4 0 row_01_08_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_04

theorem row_01_08_02_05 : b4RowContribution (![1, 9, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 11, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 11 + 16 = 37
    decide
  have hzsq : (∑ i, (((![1, 9, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 11^2 + 16^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_02_05

theorem weighted_01_08_02_05 : b4RawGapContribution ![1, 8, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 2, 5] = b4GapPatternWeight 8 2 5 * 0 :=
      b4GapContribution_from_row 1 8 2 5 0 row_01_08_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_02_05

def dvalues_01_08_02 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_08_02

theorem dblock_01_08_02 : b4GapPatternDBlock 1 8 2 = 0 := by
  calc
    b4GapPatternDBlock 1 8 2 = ∑ d : Fin 6, dvalues_01_08_02 d := by
      apply b4GapDBlock_of_rows 1 8 2 dvalues_01_08_02
      intro d
      fin_cases d
      · exact weighted_01_08_02_00
      · exact weighted_01_08_02_01
      · exact weighted_01_08_02_02
      · exact weighted_01_08_02_03
      · exact weighted_01_08_02_04
      · exact weighted_01_08_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_08_02

end Paper7MomentGapNumeric
