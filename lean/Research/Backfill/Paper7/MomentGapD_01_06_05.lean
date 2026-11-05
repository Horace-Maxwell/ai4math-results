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

theorem row_01_06_05_00 : b4RowContribution (![1, 7, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 12 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 12^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_00

theorem weighted_01_06_05_00 : b4RawGapContribution ![1, 6, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 0] = b4GapPatternWeight 6 5 0 * 0 :=
      b4GapContribution_from_row 1 6 5 0 0 row_01_06_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_00

theorem row_01_06_05_01 : b4RowContribution (![1, 7, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 13 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 13^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_01

theorem weighted_01_06_05_01 : b4RawGapContribution ![1, 6, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 1] = b4GapPatternWeight 6 5 1 * 0 :=
      b4GapContribution_from_row 1 6 5 1 0 row_01_06_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_01

theorem row_01_06_05_02 : b4RowContribution (![1, 7, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 14 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 14^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_02

theorem weighted_01_06_05_02 : b4RawGapContribution ![1, 6, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 2] = b4GapPatternWeight 6 5 2 * 0 :=
      b4GapContribution_from_row 1 6 5 2 0 row_01_06_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_02

theorem row_01_06_05_03 : b4RowContribution (![1, 7, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 15 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 15^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_03

theorem weighted_01_06_05_03 : b4RawGapContribution ![1, 6, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 3] = b4GapPatternWeight 6 5 3 * 0 :=
      b4GapContribution_from_row 1 6 5 3 0 row_01_06_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_03

theorem row_01_06_05_04 : b4RowContribution (![1, 7, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 16 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 16^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_04

theorem weighted_01_06_05_04 : b4RawGapContribution ![1, 6, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 4] = b4GapPatternWeight 6 5 4 * 0 :=
      b4GapContribution_from_row 1 6 5 4 0 row_01_06_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_04

theorem row_01_06_05_05 : b4RowContribution (![1, 7, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 12, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 12 + 17 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 12^2 + 17^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_05_05

theorem weighted_01_06_05_05 : b4RawGapContribution ![1, 6, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 5, 5] = b4GapPatternWeight 6 5 5 * 0 :=
      b4GapContribution_from_row 1 6 5 5 0 row_01_06_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_05_05

def dvalues_01_06_05 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_05

theorem dblock_01_06_05 : b4GapPatternDBlock 1 6 5 = 0 := by
  calc
    b4GapPatternDBlock 1 6 5 = ∑ d : Fin 6, dvalues_01_06_05 d := by
      apply b4GapDBlock_of_rows 1 6 5 dvalues_01_06_05
      intro d
      fin_cases d
      · exact weighted_01_06_05_00
      · exact weighted_01_06_05_01
      · exact weighted_01_06_05_02
      · exact weighted_01_06_05_03
      · exact weighted_01_06_05_04
      · exact weighted_01_06_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_05

end Paper7MomentGapNumeric
