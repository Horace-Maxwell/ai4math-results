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

theorem row_01_04_07_00 : b4RowContribution (![1, 5, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 12 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 12^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_00

theorem weighted_01_04_07_00 : b4RawGapContribution ![1, 4, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 0] = b4GapPatternWeight 4 7 0 * 0 :=
      b4GapContribution_from_row 1 4 7 0 0 row_01_04_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_00

theorem row_01_04_07_01 : b4RowContribution (![1, 5, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 13 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 13^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_01

theorem weighted_01_04_07_01 : b4RawGapContribution ![1, 4, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 1] = b4GapPatternWeight 4 7 1 * 0 :=
      b4GapContribution_from_row 1 4 7 1 0 row_01_04_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_01

theorem row_01_04_07_02 : b4RowContribution (![1, 5, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 14 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 14^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_02

theorem weighted_01_04_07_02 : b4RawGapContribution ![1, 4, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 2] = b4GapPatternWeight 4 7 2 * 0 :=
      b4GapContribution_from_row 1 4 7 2 0 row_01_04_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_02

theorem row_01_04_07_03 : b4RowContribution (![1, 5, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 15 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 15^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_03

theorem weighted_01_04_07_03 : b4RawGapContribution ![1, 4, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 3] = b4GapPatternWeight 4 7 3 * 0 :=
      b4GapContribution_from_row 1 4 7 3 0 row_01_04_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_03

theorem row_01_04_07_04 : b4RowContribution (![1, 5, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 16 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 16^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_04

theorem weighted_01_04_07_04 : b4RawGapContribution ![1, 4, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 4] = b4GapPatternWeight 4 7 4 * 0 :=
      b4GapContribution_from_row 1 4 7 4 0 row_01_04_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_04

theorem row_01_04_07_05 : b4RowContribution (![1, 5, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 17 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 17^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_05

theorem weighted_01_04_07_05 : b4RawGapContribution ![1, 4, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 5] = b4GapPatternWeight 4 7 5 * 0 :=
      b4GapContribution_from_row 1 4 7 5 0 row_01_04_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_05

theorem row_01_04_07_06 : b4RowContribution (![1, 5, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 18 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 18^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_06

theorem weighted_01_04_07_06 : b4RawGapContribution ![1, 4, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 6] = b4GapPatternWeight 4 7 6 * 0 :=
      b4GapContribution_from_row 1 4 7 6 0 row_01_04_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_06

theorem row_01_04_07_07 : b4RowContribution (![1, 5, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 12, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 12 + 19 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 12^2 + 19^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_07_07

theorem weighted_01_04_07_07 : b4RawGapContribution ![1, 4, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 7, 7] = b4GapPatternWeight 4 7 7 * 0 :=
      b4GapContribution_from_row 1 4 7 7 0 row_01_04_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_07_07

def dvalues_01_04_07 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_07

theorem dblock_01_04_07 : b4GapPatternDBlock 1 4 7 = 0 := by
  calc
    b4GapPatternDBlock 1 4 7 = ∑ d : Fin 8, dvalues_01_04_07 d := by
      apply b4GapDBlock_of_rows 1 4 7 dvalues_01_04_07
      intro d
      fin_cases d
      · exact weighted_01_04_07_00
      · exact weighted_01_04_07_01
      · exact weighted_01_04_07_02
      · exact weighted_01_04_07_03
      · exact weighted_01_04_07_04
      · exact weighted_01_04_07_05
      · exact weighted_01_04_07_06
      · exact weighted_01_04_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_07

end Paper7MomentGapNumeric
