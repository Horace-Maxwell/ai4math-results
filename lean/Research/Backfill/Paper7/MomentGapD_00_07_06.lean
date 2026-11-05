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

theorem row_00_07_06_00 : b4RowContribution (![0, 7, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 13, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 13 + 13 = 33
    decide
  have hzsq : (∑ i, (((![0, 7, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 13^2 + 13^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_06_00

theorem weighted_00_07_06_00 : b4RawGapContribution ![0, 7, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 6, 0] = b4GapPatternWeight 7 6 0 * 0 :=
      b4GapContribution_from_row 0 7 6 0 0 row_00_07_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_06_00

theorem row_00_07_06_01 : b4RowContribution (![0, 7, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 13, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 13 + 14 = 34
    decide
  have hzsq : (∑ i, (((![0, 7, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 13^2 + 14^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_06_01

theorem weighted_00_07_06_01 : b4RawGapContribution ![0, 7, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 6, 1] = b4GapPatternWeight 7 6 1 * 0 :=
      b4GapContribution_from_row 0 7 6 1 0 row_00_07_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_06_01

theorem row_00_07_06_02 : b4RowContribution (![0, 7, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 13, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 13 + 15 = 35
    decide
  have hzsq : (∑ i, (((![0, 7, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 13^2 + 15^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_06_02

theorem weighted_00_07_06_02 : b4RawGapContribution ![0, 7, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 6, 2] = b4GapPatternWeight 7 6 2 * 0 :=
      b4GapContribution_from_row 0 7 6 2 0 row_00_07_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_06_02

theorem row_00_07_06_03 : b4RowContribution (![0, 7, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 13, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 13 + 16 = 36
    decide
  have hzsq : (∑ i, (((![0, 7, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 13^2 + 16^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_06_03

theorem weighted_00_07_06_03 : b4RawGapContribution ![0, 7, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 6, 3] = b4GapPatternWeight 7 6 3 * 0 :=
      b4GapContribution_from_row 0 7 6 3 0 row_00_07_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_06_03

theorem row_00_07_06_04 : b4RowContribution (![0, 7, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 13, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 13 + 17 = 37
    decide
  have hzsq : (∑ i, (((![0, 7, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 13^2 + 17^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_06_04

theorem weighted_00_07_06_04 : b4RawGapContribution ![0, 7, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 6, 4] = b4GapPatternWeight 7 6 4 * 0 :=
      b4GapContribution_from_row 0 7 6 4 0 row_00_07_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_06_04

def dvalues_00_07_06 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_07_06

theorem dblock_00_07_06 : b4GapPatternDBlock 0 7 6 = 0 := by
  calc
    b4GapPatternDBlock 0 7 6 = ∑ d : Fin 5, dvalues_00_07_06 d := by
      apply b4GapDBlock_of_rows 0 7 6 dvalues_00_07_06
      intro d
      fin_cases d
      · exact weighted_00_07_06_00
      · exact weighted_00_07_06_01
      · exact weighted_00_07_06_02
      · exact weighted_00_07_06_03
      · exact weighted_00_07_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_07_06

end Paper7MomentGapNumeric
