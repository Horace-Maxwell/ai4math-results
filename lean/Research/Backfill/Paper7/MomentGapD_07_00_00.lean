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

theorem row_07_00_00_00 : b4RowContribution (![7, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 7] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 7 = 28
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_00

theorem weighted_07_00_00_00 : b4RawGapContribution ![7, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 7 0 0 0 0 row_07_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_00

theorem row_07_00_00_01 : b4RowContribution (![7, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 8] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 8 = 29
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_01

theorem weighted_07_00_00_01 : b4RawGapContribution ![7, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 7 0 0 1 0 row_07_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_01

theorem row_07_00_00_02 : b4RowContribution (![7, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 9] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 9 = 30
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 228
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_02

theorem weighted_07_00_00_02 : b4RawGapContribution ![7, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 7 0 0 2 0 row_07_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_02

theorem row_07_00_00_03 : b4RowContribution (![7, 7, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 10 = 31
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_03

theorem weighted_07_00_00_03 : b4RawGapContribution ![7, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 7 0 0 3 0 row_07_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_03

theorem row_07_00_00_04 : b4RowContribution (![7, 7, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 11 = 32
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_04

theorem weighted_07_00_00_04 : b4RawGapContribution ![7, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 7 0 0 4 0 row_07_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_04

theorem row_07_00_00_05 : b4RowContribution (![7, 7, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 12 = 33
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 291
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_05

theorem weighted_07_00_00_05 : b4RawGapContribution ![7, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 7 0 0 5 0 row_07_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_05

theorem row_07_00_00_06 : b4RowContribution (![7, 7, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 13 = 34
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_06

theorem weighted_07_00_00_06 : b4RawGapContribution ![7, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 7 0 0 6 0 row_07_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_06

theorem row_07_00_00_07 : b4RowContribution (![7, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 14 = 35
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_07

theorem weighted_07_00_00_07 : b4RawGapContribution ![7, 0, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 0 :=
      b4GapContribution_from_row 7 0 0 7 0 row_07_00_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_07

theorem row_07_00_00_08 : b4RowContribution (![7, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 15 = 36
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_08

theorem weighted_07_00_00_08 : b4RawGapContribution ![7, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 7 0 0 8 0 row_07_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_08

theorem row_07_00_00_09 : b4RowContribution (![7, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 7, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 7 + 16 = 37
    decide
  have hzsq : (∑ i, (((![7, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_00_09

theorem weighted_07_00_00_09 : b4RawGapContribution ![7, 0, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 0 :=
      b4GapContribution_from_row 7 0 0 9 0 row_07_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_00_09

def dvalues_07_00_00 : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_00_00

theorem dblock_07_00_00 : b4GapPatternDBlock 7 0 0 = 0 := by
  calc
    b4GapPatternDBlock 7 0 0 = ∑ d : Fin 10, dvalues_07_00_00 d := by
      apply b4GapDBlock_of_rows 7 0 0 dvalues_07_00_00
      intro d
      fin_cases d
      · exact weighted_07_00_00_00
      · exact weighted_07_00_00_01
      · exact weighted_07_00_00_02
      · exact weighted_07_00_00_03
      · exact weighted_07_00_00_04
      · exact weighted_07_00_00_05
      · exact weighted_07_00_00_06
      · exact weighted_07_00_00_07
      · exact weighted_07_00_00_08
      · exact weighted_07_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_00_00

end Paper7MomentGapNumeric
