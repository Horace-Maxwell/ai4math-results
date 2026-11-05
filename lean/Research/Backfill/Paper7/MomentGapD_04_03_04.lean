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

theorem row_04_03_04_00 : b4RowContribution (![4, 7, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 11, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 11 + 11 = 33
    decide
  have hzsq : (∑ i, (((![4, 7, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 11^2 + 11^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_04_00

theorem weighted_04_03_04_00 : b4RawGapContribution ![4, 3, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 4, 0] = b4GapPatternWeight 3 4 0 * 0 :=
      b4GapContribution_from_row 4 3 4 0 0 row_04_03_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_04_00

theorem row_04_03_04_01 : b4RowContribution (![4, 7, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 11, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 11 + 12 = 34
    decide
  have hzsq : (∑ i, (((![4, 7, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 11^2 + 12^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_04_01

theorem weighted_04_03_04_01 : b4RawGapContribution ![4, 3, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 4, 1] = b4GapPatternWeight 3 4 1 * 0 :=
      b4GapContribution_from_row 4 3 4 1 0 row_04_03_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_04_01

theorem row_04_03_04_02 : b4RowContribution (![4, 7, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 11, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 11 + 13 = 35
    decide
  have hzsq : (∑ i, (((![4, 7, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 11^2 + 13^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_04_02

theorem weighted_04_03_04_02 : b4RawGapContribution ![4, 3, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 4, 2] = b4GapPatternWeight 3 4 2 * 0 :=
      b4GapContribution_from_row 4 3 4 2 0 row_04_03_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_04_02

theorem row_04_03_04_03 : b4RowContribution (![4, 7, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 11, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 11 + 14 = 36
    decide
  have hzsq : (∑ i, (((![4, 7, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 11^2 + 14^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_04_03

theorem weighted_04_03_04_03 : b4RawGapContribution ![4, 3, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 4, 3] = b4GapPatternWeight 3 4 3 * 0 :=
      b4GapContribution_from_row 4 3 4 3 0 row_04_03_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_04_03

theorem row_04_03_04_04 : b4RowContribution (![4, 7, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 11, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 11 + 15 = 37
    decide
  have hzsq : (∑ i, (((![4, 7, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 11^2 + 15^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_04_04

theorem weighted_04_03_04_04 : b4RawGapContribution ![4, 3, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 4, 4] = b4GapPatternWeight 3 4 4 * 0 :=
      b4GapContribution_from_row 4 3 4 4 0 row_04_03_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_04_04

def dvalues_04_03_04 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_03_04

theorem dblock_04_03_04 : b4GapPatternDBlock 4 3 4 = 0 := by
  calc
    b4GapPatternDBlock 4 3 4 = ∑ d : Fin 5, dvalues_04_03_04 d := by
      apply b4GapDBlock_of_rows 4 3 4 dvalues_04_03_04
      intro d
      fin_cases d
      · exact weighted_04_03_04_00
      · exact weighted_04_03_04_01
      · exact weighted_04_03_04_02
      · exact weighted_04_03_04_03
      · exact weighted_04_03_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_03_04

end Paper7MomentGapNumeric
