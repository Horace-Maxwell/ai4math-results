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

theorem row_02_02_06_00 : b4RowContribution (![2, 4, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 10 = 26
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 10^2 = 220
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_00

theorem weighted_02_02_06_00 : b4RawGapContribution ![2, 2, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 0] = b4GapPatternWeight 2 6 0 * 0 :=
      b4GapContribution_from_row 2 2 6 0 0 row_02_02_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_00

theorem row_02_02_06_01 : b4RowContribution (![2, 4, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 11 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 11^2 = 241
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_01

theorem weighted_02_02_06_01 : b4RawGapContribution ![2, 2, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 1] = b4GapPatternWeight 2 6 1 * 0 :=
      b4GapContribution_from_row 2 2 6 1 0 row_02_02_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_01

theorem row_02_02_06_02 : b4RowContribution (![2, 4, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 12 = 28
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 264 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 12^2 = 264
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_02

theorem weighted_02_02_06_02 : b4RawGapContribution ![2, 2, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 2] = b4GapPatternWeight 2 6 2 * 0 :=
      b4GapContribution_from_row 2 2 6 2 0 row_02_02_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_02

theorem row_02_02_06_03 : b4RowContribution (![2, 4, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 13 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 13^2 = 289
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_03

theorem weighted_02_02_06_03 : b4RawGapContribution ![2, 2, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 3] = b4GapPatternWeight 2 6 3 * 0 :=
      b4GapContribution_from_row 2 2 6 3 0 row_02_02_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_03

theorem row_02_02_06_04 : b4RowContribution (![2, 4, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 14 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 14^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_04

theorem weighted_02_02_06_04 : b4RawGapContribution ![2, 2, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 4] = b4GapPatternWeight 2 6 4 * 0 :=
      b4GapContribution_from_row 2 2 6 4 0 row_02_02_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_04

theorem row_02_02_06_05 : b4RowContribution (![2, 4, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 15 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 15^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_05

theorem weighted_02_02_06_05 : b4RawGapContribution ![2, 2, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 5] = b4GapPatternWeight 2 6 5 * 0 :=
      b4GapContribution_from_row 2 2 6 5 0 row_02_02_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_05

theorem row_02_02_06_06 : b4RowContribution (![2, 4, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 16 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 376 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 16^2 = 376
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_06

theorem weighted_02_02_06_06 : b4RawGapContribution ![2, 2, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 6] = b4GapPatternWeight 2 6 6 * 0 :=
      b4GapContribution_from_row 2 2 6 6 0 row_02_02_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_06

theorem row_02_02_06_07 : b4RowContribution (![2, 4, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 17 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 17^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_07

theorem weighted_02_02_06_07 : b4RawGapContribution ![2, 2, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 7] = b4GapPatternWeight 2 6 7 * 0 :=
      b4GapContribution_from_row 2 2 6 7 0 row_02_02_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_07

theorem row_02_02_06_08 : b4RowContribution (![2, 4, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 18 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 18^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_08

theorem weighted_02_02_06_08 : b4RawGapContribution ![2, 2, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 8] = b4GapPatternWeight 2 6 8 * 0 :=
      b4GapContribution_from_row 2 2 6 8 0 row_02_02_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_08

theorem row_02_02_06_09 : b4RowContribution (![2, 4, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 19 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 481 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 19^2 = 481
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_09

theorem weighted_02_02_06_09 : b4RawGapContribution ![2, 2, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 9] = b4GapPatternWeight 2 6 9 * 0 :=
      b4GapContribution_from_row 2 2 6 9 0 row_02_02_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_09

theorem row_02_02_06_10 : b4RowContribution (![2, 4, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 20 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 520 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 20^2 = 520
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_10

theorem weighted_02_02_06_10 : b4RawGapContribution ![2, 2, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 10] = b4GapPatternWeight 2 6 10 * 0 :=
      b4GapContribution_from_row 2 2 6 10 0 row_02_02_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_10

theorem row_02_02_06_11 : b4RowContribution (![2, 4, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 10, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 10 + 21 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 561 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 10^2 + 21^2 = 561
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_06_11

theorem weighted_02_02_06_11 : b4RawGapContribution ![2, 2, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 6, 11] = b4GapPatternWeight 2 6 11 * 0 :=
      b4GapContribution_from_row 2 2 6 11 0 row_02_02_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_06_11

def dvalues_02_02_06 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_06

theorem dblock_02_02_06 : b4GapPatternDBlock 2 2 6 = 0 := by
  calc
    b4GapPatternDBlock 2 2 6 = ∑ d : Fin 12, dvalues_02_02_06 d := by
      apply b4GapDBlock_of_rows 2 2 6 dvalues_02_02_06
      intro d
      fin_cases d
      · exact weighted_02_02_06_00
      · exact weighted_02_02_06_01
      · exact weighted_02_02_06_02
      · exact weighted_02_02_06_03
      · exact weighted_02_02_06_04
      · exact weighted_02_02_06_05
      · exact weighted_02_02_06_06
      · exact weighted_02_02_06_07
      · exact weighted_02_02_06_08
      · exact weighted_02_02_06_09
      · exact weighted_02_02_06_10
      · exact weighted_02_02_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_06

end Paper7MomentGapNumeric
