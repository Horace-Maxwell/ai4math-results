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

theorem row_01_05_06_00 : b4RowContribution (![1, 6, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 12 = 31
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 12^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_00

theorem weighted_01_05_06_00 : b4RawGapContribution ![1, 5, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 0] = b4GapPatternWeight 5 6 0 * 0 :=
      b4GapContribution_from_row 1 5 6 0 0 row_01_05_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_00

theorem row_01_05_06_01 : b4RowContribution (![1, 6, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 13 = 32
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 13^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_01

theorem weighted_01_05_06_01 : b4RawGapContribution ![1, 5, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 1] = b4GapPatternWeight 5 6 1 * 0 :=
      b4GapContribution_from_row 1 5 6 1 0 row_01_05_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_01

theorem row_01_05_06_02 : b4RowContribution (![1, 6, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 14 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 14^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_02

theorem weighted_01_05_06_02 : b4RawGapContribution ![1, 5, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 2] = b4GapPatternWeight 5 6 2 * 0 :=
      b4GapContribution_from_row 1 5 6 2 0 row_01_05_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_02

theorem row_01_05_06_03 : b4RowContribution (![1, 6, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 15 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 15^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_03

theorem weighted_01_05_06_03 : b4RawGapContribution ![1, 5, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 3] = b4GapPatternWeight 5 6 3 * 0 :=
      b4GapContribution_from_row 1 5 6 3 0 row_01_05_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_03

theorem row_01_05_06_04 : b4RowContribution (![1, 6, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 16^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_04

theorem weighted_01_05_06_04 : b4RawGapContribution ![1, 5, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 4] = b4GapPatternWeight 5 6 4 * 0 :=
      b4GapContribution_from_row 1 5 6 4 0 row_01_05_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_04

theorem row_01_05_06_05 : b4RowContribution (![1, 6, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 17^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_05

theorem weighted_01_05_06_05 : b4RawGapContribution ![1, 5, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 5] = b4GapPatternWeight 5 6 5 * 0 :=
      b4GapContribution_from_row 1 5 6 5 0 row_01_05_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_05

theorem row_01_05_06_06 : b4RowContribution (![1, 6, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 12, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 12 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 12^2 + 18^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_06_06

theorem weighted_01_05_06_06 : b4RawGapContribution ![1, 5, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 6, 6] = b4GapPatternWeight 5 6 6 * 0 :=
      b4GapContribution_from_row 1 5 6 6 0 row_01_05_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_06_06

def dvalues_01_05_06 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_06

theorem dblock_01_05_06 : b4GapPatternDBlock 1 5 6 = 0 := by
  calc
    b4GapPatternDBlock 1 5 6 = ∑ d : Fin 7, dvalues_01_05_06 d := by
      apply b4GapDBlock_of_rows 1 5 6 dvalues_01_05_06
      intro d
      fin_cases d
      · exact weighted_01_05_06_00
      · exact weighted_01_05_06_01
      · exact weighted_01_05_06_02
      · exact weighted_01_05_06_03
      · exact weighted_01_05_06_04
      · exact weighted_01_05_06_05
      · exact weighted_01_05_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_06

end Paper7MomentGapNumeric
