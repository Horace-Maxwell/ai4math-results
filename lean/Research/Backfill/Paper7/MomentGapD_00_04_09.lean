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

theorem row_00_04_09_00 : b4RowContribution (![0, 4, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 13 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 13^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_00

theorem weighted_00_04_09_00 : b4RawGapContribution ![0, 4, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 0] = b4GapPatternWeight 4 9 0 * 0 :=
      b4GapContribution_from_row 0 4 9 0 0 row_00_04_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_00

theorem row_00_04_09_01 : b4RowContribution (![0, 4, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 14^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_01

theorem weighted_00_04_09_01 : b4RawGapContribution ![0, 4, 9, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 1] = b4GapPatternWeight 4 9 1 * 0 :=
      b4GapContribution_from_row 0 4 9 1 0 row_00_04_09_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_01

theorem row_00_04_09_02 : b4RowContribution (![0, 4, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 15^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_02

theorem weighted_00_04_09_02 : b4RawGapContribution ![0, 4, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 2] = b4GapPatternWeight 4 9 2 * 0 :=
      b4GapContribution_from_row 0 4 9 2 0 row_00_04_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_02

theorem row_00_04_09_03 : b4RowContribution (![0, 4, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 16^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_03

theorem weighted_00_04_09_03 : b4RawGapContribution ![0, 4, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 3] = b4GapPatternWeight 4 9 3 * 0 :=
      b4GapContribution_from_row 0 4 9 3 0 row_00_04_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_03

theorem row_00_04_09_04 : b4RowContribution (![0, 4, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 17^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_04

theorem weighted_00_04_09_04 : b4RawGapContribution ![0, 4, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 4] = b4GapPatternWeight 4 9 4 * 0 :=
      b4GapContribution_from_row 0 4 9 4 0 row_00_04_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_04

theorem row_00_04_09_05 : b4RowContribution (![0, 4, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 509 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 18^2 = 509
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_05

theorem weighted_00_04_09_05 : b4RawGapContribution ![0, 4, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 5] = b4GapPatternWeight 4 9 5 * 0 :=
      b4GapContribution_from_row 0 4 9 5 0 row_00_04_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_05

theorem row_00_04_09_06 : b4RowContribution (![0, 4, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 19^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_06

theorem weighted_00_04_09_06 : b4RawGapContribution ![0, 4, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 6] = b4GapPatternWeight 4 9 6 * 0 :=
      b4GapContribution_from_row 0 4 9 6 0 row_00_04_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_06

theorem row_00_04_09_07 : b4RowContribution (![0, 4, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 13, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 13 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 13^2 + 20^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_09_07

theorem weighted_00_04_09_07 : b4RawGapContribution ![0, 4, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 9, 7] = b4GapPatternWeight 4 9 7 * 0 :=
      b4GapContribution_from_row 0 4 9 7 0 row_00_04_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_09_07

def dvalues_00_04_09 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_09

theorem dblock_00_04_09 : b4GapPatternDBlock 0 4 9 = 0 := by
  calc
    b4GapPatternDBlock 0 4 9 = ∑ d : Fin 8, dvalues_00_04_09 d := by
      apply b4GapDBlock_of_rows 0 4 9 dvalues_00_04_09
      intro d
      fin_cases d
      · exact weighted_00_04_09_00
      · exact weighted_00_04_09_01
      · exact weighted_00_04_09_02
      · exact weighted_00_04_09_03
      · exact weighted_00_04_09_04
      · exact weighted_00_04_09_05
      · exact weighted_00_04_09_06
      · exact weighted_00_04_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_09

end Paper7MomentGapNumeric
