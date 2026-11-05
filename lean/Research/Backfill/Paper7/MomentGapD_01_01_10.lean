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

theorem row_01_01_10_00 : b4RowContribution (![1, 2, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 12 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 12^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_00

theorem weighted_01_01_10_00 : b4RawGapContribution ![1, 1, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 0] = b4GapPatternWeight 1 10 0 * 0 :=
      b4GapContribution_from_row 1 1 10 0 0 row_01_01_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_00

theorem row_01_01_10_01 : b4RowContribution (![1, 2, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 13 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 13^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_01

theorem weighted_01_01_10_01 : b4RawGapContribution ![1, 1, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 1] = b4GapPatternWeight 1 10 1 * 0 :=
      b4GapContribution_from_row 1 1 10 1 0 row_01_01_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_01

theorem row_01_01_10_02 : b4RowContribution (![1, 2, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 14^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_02

theorem weighted_01_01_10_02 : b4RawGapContribution ![1, 1, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 2] = b4GapPatternWeight 1 10 2 * 0 :=
      b4GapContribution_from_row 1 1 10 2 0 row_01_01_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_02

theorem row_01_01_10_03 : b4RowContribution (![1, 2, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 15^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_03

theorem weighted_01_01_10_03 : b4RawGapContribution ![1, 1, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 3] = b4GapPatternWeight 1 10 3 * 0 :=
      b4GapContribution_from_row 1 1 10 3 0 row_01_01_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_03

theorem row_01_01_10_04 : b4RowContribution (![1, 2, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 16^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_04

theorem weighted_01_01_10_04 : b4RawGapContribution ![1, 1, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 4] = b4GapPatternWeight 1 10 4 * 0 :=
      b4GapContribution_from_row 1 1 10 4 0 row_01_01_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_04

theorem row_01_01_10_05 : b4RowContribution (![1, 2, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 17^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_05

theorem weighted_01_01_10_05 : b4RawGapContribution ![1, 1, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 5] = b4GapPatternWeight 1 10 5 * 0 :=
      b4GapContribution_from_row 1 1 10 5 0 row_01_01_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_05

theorem row_01_01_10_06 : b4RowContribution (![1, 2, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 18^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_06

theorem weighted_01_01_10_06 : b4RawGapContribution ![1, 1, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 6] = b4GapPatternWeight 1 10 6 * 0 :=
      b4GapContribution_from_row 1 1 10 6 0 row_01_01_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_06

theorem row_01_01_10_07 : b4RowContribution (![1, 2, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 19^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_07

theorem weighted_01_01_10_07 : b4RawGapContribution ![1, 1, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 7] = b4GapPatternWeight 1 10 7 * 0 :=
      b4GapContribution_from_row 1 1 10 7 0 row_01_01_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_07

theorem row_01_01_10_08 : b4RowContribution (![1, 2, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 20^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_08

theorem weighted_01_01_10_08 : b4RawGapContribution ![1, 1, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 8] = b4GapPatternWeight 1 10 8 * 0 :=
      b4GapContribution_from_row 1 1 10 8 0 row_01_01_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_08

theorem row_01_01_10_09 : b4RowContribution (![1, 2, 12, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 590 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 21^2 = 590
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_09

theorem weighted_01_01_10_09 : b4RawGapContribution ![1, 1, 10, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 9] = b4GapPatternWeight 1 10 9 * 0 :=
      b4GapContribution_from_row 1 1 10 9 0 row_01_01_10_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_09

theorem row_01_01_10_10 : b4RowContribution (![1, 2, 12, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 12, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 12 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 12, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 633 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 12^2 + 22^2 = 633
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_10_10

theorem weighted_01_01_10_10 : b4RawGapContribution ![1, 1, 10, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 10, 10] = b4GapPatternWeight 1 10 10 * 0 :=
      b4GapContribution_from_row 1 1 10 10 0 row_01_01_10_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_10_10

def dvalues_01_01_10 : Fin 11 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_10

theorem dblock_01_01_10 : b4GapPatternDBlock 1 1 10 = 0 := by
  calc
    b4GapPatternDBlock 1 1 10 = ∑ d : Fin 11, dvalues_01_01_10 d := by
      apply b4GapDBlock_of_rows 1 1 10 dvalues_01_01_10
      intro d
      fin_cases d
      · exact weighted_01_01_10_00
      · exact weighted_01_01_10_01
      · exact weighted_01_01_10_02
      · exact weighted_01_01_10_03
      · exact weighted_01_01_10_04
      · exact weighted_01_01_10_05
      · exact weighted_01_01_10_06
      · exact weighted_01_01_10_07
      · exact weighted_01_01_10_08
      · exact weighted_01_01_10_09
      · exact weighted_01_01_10_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_10

end Paper7MomentGapNumeric
