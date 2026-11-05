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

theorem row_05_02_03_00 : b4RowContribution (![5, 7, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 10] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 10 = 32
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 10^2 = 274
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_00

theorem weighted_05_02_03_00 : b4RawGapContribution ![5, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 5 2 3 0 0 row_05_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_00

theorem row_05_02_03_01 : b4RowContribution (![5, 7, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 11 = 33
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 11^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_01

theorem weighted_05_02_03_01 : b4RawGapContribution ![5, 2, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 0 :=
      b4GapContribution_from_row 5 2 3 1 0 row_05_02_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_01

theorem row_05_02_03_02 : b4RowContribution (![5, 7, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 12 = 34
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 12^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_02

theorem weighted_05_02_03_02 : b4RawGapContribution ![5, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 5 2 3 2 0 row_05_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_02

theorem row_05_02_03_03 : b4RowContribution (![5, 7, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 13 = 35
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 13^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_03

theorem weighted_05_02_03_03 : b4RawGapContribution ![5, 2, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 0 :=
      b4GapContribution_from_row 5 2 3 3 0 row_05_02_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_03

theorem row_05_02_03_04 : b4RowContribution (![5, 7, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 14 = 36
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 14^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_04

theorem weighted_05_02_03_04 : b4RawGapContribution ![5, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 5 2 3 4 0 row_05_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_04

theorem row_05_02_03_05 : b4RowContribution (![5, 7, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 10, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 10 + 15 = 37
    decide
  have hzsq : (∑ i, (((![5, 7, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 10^2 + 15^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_03_05

theorem weighted_05_02_03_05 : b4RawGapContribution ![5, 2, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 0 :=
      b4GapContribution_from_row 5 2 3 5 0 row_05_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_03_05

def dvalues_05_02_03 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_02_03

theorem dblock_05_02_03 : b4GapPatternDBlock 5 2 3 = 0 := by
  calc
    b4GapPatternDBlock 5 2 3 = ∑ d : Fin 6, dvalues_05_02_03 d := by
      apply b4GapDBlock_of_rows 5 2 3 dvalues_05_02_03
      intro d
      fin_cases d
      · exact weighted_05_02_03_00
      · exact weighted_05_02_03_01
      · exact weighted_05_02_03_02
      · exact weighted_05_02_03_03
      · exact weighted_05_02_03_04
      · exact weighted_05_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_02_03

end Paper7MomentGapNumeric
