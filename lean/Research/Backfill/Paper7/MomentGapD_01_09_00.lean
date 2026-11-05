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

theorem row_01_09_00_00 : b4RowContribution (![1, 10, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 10 = 31
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 10^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_00

theorem weighted_01_09_00_00 : b4RawGapContribution ![1, 9, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 0] = b4GapPatternWeight 9 0 0 * 0 :=
      b4GapContribution_from_row 1 9 0 0 0 row_01_09_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_00

theorem row_01_09_00_01 : b4RowContribution (![1, 10, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 11 = 32
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 11^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_01

theorem weighted_01_09_00_01 : b4RawGapContribution ![1, 9, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 1] = b4GapPatternWeight 9 0 1 * 0 :=
      b4GapContribution_from_row 1 9 0 1 0 row_01_09_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_01

theorem row_01_09_00_02 : b4RowContribution (![1, 10, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 12 = 33
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 12^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_02

theorem weighted_01_09_00_02 : b4RawGapContribution ![1, 9, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 2] = b4GapPatternWeight 9 0 2 * 0 :=
      b4GapContribution_from_row 1 9 0 2 0 row_01_09_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_02

theorem row_01_09_00_03 : b4RowContribution (![1, 10, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 13 = 34
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 13^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_03

theorem weighted_01_09_00_03 : b4RawGapContribution ![1, 9, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 3] = b4GapPatternWeight 9 0 3 * 0 :=
      b4GapContribution_from_row 1 9 0 3 0 row_01_09_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_03

theorem row_01_09_00_04 : b4RowContribution (![1, 10, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 14 = 35
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 14^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_04

theorem weighted_01_09_00_04 : b4RawGapContribution ![1, 9, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 4] = b4GapPatternWeight 9 0 4 * 0 :=
      b4GapContribution_from_row 1 9 0 4 0 row_01_09_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_04

theorem row_01_09_00_05 : b4RowContribution (![1, 10, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 15 = 36
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 15^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_05

theorem weighted_01_09_00_05 : b4RawGapContribution ![1, 9, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 5] = b4GapPatternWeight 9 0 5 * 0 :=
      b4GapContribution_from_row 1 9 0 5 0 row_01_09_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_05

theorem row_01_09_00_06 : b4RowContribution (![1, 10, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 10, 10, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 10 + 10 + 16 = 37
    decide
  have hzsq : (∑ i, (((![1, 10, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 10^2 + 10^2 + 16^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_09_00_06

theorem weighted_01_09_00_06 : b4RawGapContribution ![1, 9, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 9, 0, 6] = b4GapPatternWeight 9 0 6 * 0 :=
      b4GapContribution_from_row 1 9 0 6 0 row_01_09_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_09_00_06

def dvalues_01_09_00 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_09_00

theorem dblock_01_09_00 : b4GapPatternDBlock 1 9 0 = 0 := by
  calc
    b4GapPatternDBlock 1 9 0 = ∑ d : Fin 7, dvalues_01_09_00 d := by
      apply b4GapDBlock_of_rows 1 9 0 dvalues_01_09_00
      intro d
      fin_cases d
      · exact weighted_01_09_00_00
      · exact weighted_01_09_00_01
      · exact weighted_01_09_00_02
      · exact weighted_01_09_00_03
      · exact weighted_01_09_00_04
      · exact weighted_01_09_00_05
      · exact weighted_01_09_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_09_00

end Paper7MomentGapNumeric
