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

theorem row_00_05_06_00 : b4RowContribution (![0, 5, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 11 = 27
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 11^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_00

theorem weighted_00_05_06_00 : b4RawGapContribution ![0, 5, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 0] = b4GapPatternWeight 5 6 0 * 0 :=
      b4GapContribution_from_row 0 5 6 0 0 row_00_05_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_00

theorem row_00_05_06_01 : b4RowContribution (![0, 5, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 12 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 12^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_01

theorem weighted_00_05_06_01 : b4RawGapContribution ![0, 5, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 1] = b4GapPatternWeight 5 6 1 * 0 :=
      b4GapContribution_from_row 0 5 6 1 0 row_00_05_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_01

theorem row_00_05_06_02 : b4RowContribution (![0, 5, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 13 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 13^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_02

theorem weighted_00_05_06_02 : b4RawGapContribution ![0, 5, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 2] = b4GapPatternWeight 5 6 2 * 0 :=
      b4GapContribution_from_row 0 5 6 2 0 row_00_05_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_02

theorem row_00_05_06_03 : b4RowContribution (![0, 5, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 14^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_03

theorem weighted_00_05_06_03 : b4RawGapContribution ![0, 5, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 3] = b4GapPatternWeight 5 6 3 * 0 :=
      b4GapContribution_from_row 0 5 6 3 0 row_00_05_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_03

theorem row_00_05_06_04 : b4RowContribution (![0, 5, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 15^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_04

theorem weighted_00_05_06_04 : b4RawGapContribution ![0, 5, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 4] = b4GapPatternWeight 5 6 4 * 0 :=
      b4GapContribution_from_row 0 5 6 4 0 row_00_05_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_04

theorem row_00_05_06_05 : b4RowContribution (![0, 5, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 16^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_05

theorem weighted_00_05_06_05 : b4RawGapContribution ![0, 5, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 5] = b4GapPatternWeight 5 6 5 * 0 :=
      b4GapContribution_from_row 0 5 6 5 0 row_00_05_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_05

theorem row_00_05_06_06 : b4RowContribution (![0, 5, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 17^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_06

theorem weighted_00_05_06_06 : b4RawGapContribution ![0, 5, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 6] = b4GapPatternWeight 5 6 6 * 0 :=
      b4GapContribution_from_row 0 5 6 6 0 row_00_05_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_06

theorem row_00_05_06_07 : b4RowContribution (![0, 5, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 18^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_07

theorem weighted_00_05_06_07 : b4RawGapContribution ![0, 5, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 7] = b4GapPatternWeight 5 6 7 * 0 :=
      b4GapContribution_from_row 0 5 6 7 0 row_00_05_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_07

theorem row_00_05_06_08 : b4RowContribution (![0, 5, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 19^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_08

theorem weighted_00_05_06_08 : b4RawGapContribution ![0, 5, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 8] = b4GapPatternWeight 5 6 8 * 0 :=
      b4GapContribution_from_row 0 5 6 8 0 row_00_05_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_08

theorem row_00_05_06_09 : b4RowContribution (![0, 5, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 20^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_09

theorem weighted_00_05_06_09 : b4RawGapContribution ![0, 5, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 9] = b4GapPatternWeight 5 6 9 * 0 :=
      b4GapContribution_from_row 0 5 6 9 0 row_00_05_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_09

theorem row_00_05_06_10 : b4RowContribution (![0, 5, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 11, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 11 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 11^2 + 21^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_06_10

theorem weighted_00_05_06_10 : b4RawGapContribution ![0, 5, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 6, 10] = b4GapPatternWeight 5 6 10 * 0 :=
      b4GapContribution_from_row 0 5 6 10 0 row_00_05_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_06_10

def dvalues_00_05_06 : Fin 11 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_06

theorem dblock_00_05_06 : b4GapPatternDBlock 0 5 6 = 0 := by
  calc
    b4GapPatternDBlock 0 5 6 = ∑ d : Fin 11, dvalues_00_05_06 d := by
      apply b4GapDBlock_of_rows 0 5 6 dvalues_00_05_06
      intro d
      fin_cases d
      · exact weighted_00_05_06_00
      · exact weighted_00_05_06_01
      · exact weighted_00_05_06_02
      · exact weighted_00_05_06_03
      · exact weighted_00_05_06_04
      · exact weighted_00_05_06_05
      · exact weighted_00_05_06_06
      · exact weighted_00_05_06_07
      · exact weighted_00_05_06_08
      · exact weighted_00_05_06_09
      · exact weighted_00_05_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_06

end Paper7MomentGapNumeric
