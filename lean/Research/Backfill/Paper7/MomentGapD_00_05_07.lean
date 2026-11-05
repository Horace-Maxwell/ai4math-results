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

theorem row_00_05_07_00 : b4RowContribution (![0, 5, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 12 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 12^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_00

theorem weighted_00_05_07_00 : b4RawGapContribution ![0, 5, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 0] = b4GapPatternWeight 5 7 0 * 0 :=
      b4GapContribution_from_row 0 5 7 0 0 row_00_05_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_00

theorem row_00_05_07_01 : b4RowContribution (![0, 5, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 13 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 13^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_01

theorem weighted_00_05_07_01 : b4RawGapContribution ![0, 5, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 1] = b4GapPatternWeight 5 7 1 * 0 :=
      b4GapContribution_from_row 0 5 7 1 0 row_00_05_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_01

theorem row_00_05_07_02 : b4RowContribution (![0, 5, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 14^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_02

theorem weighted_00_05_07_02 : b4RawGapContribution ![0, 5, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 2] = b4GapPatternWeight 5 7 2 * 0 :=
      b4GapContribution_from_row 0 5 7 2 0 row_00_05_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_02

theorem row_00_05_07_03 : b4RowContribution (![0, 5, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 15^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_03

theorem weighted_00_05_07_03 : b4RawGapContribution ![0, 5, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 3] = b4GapPatternWeight 5 7 3 * 0 :=
      b4GapContribution_from_row 0 5 7 3 0 row_00_05_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_03

theorem row_00_05_07_04 : b4RowContribution (![0, 5, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 16^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_04

theorem weighted_00_05_07_04 : b4RawGapContribution ![0, 5, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 4] = b4GapPatternWeight 5 7 4 * 0 :=
      b4GapContribution_from_row 0 5 7 4 0 row_00_05_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_04

theorem row_00_05_07_05 : b4RowContribution (![0, 5, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 17^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_05

theorem weighted_00_05_07_05 : b4RawGapContribution ![0, 5, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 5] = b4GapPatternWeight 5 7 5 * 0 :=
      b4GapContribution_from_row 0 5 7 5 0 row_00_05_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_05

theorem row_00_05_07_06 : b4RowContribution (![0, 5, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 18^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_06

theorem weighted_00_05_07_06 : b4RawGapContribution ![0, 5, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 6] = b4GapPatternWeight 5 7 6 * 0 :=
      b4GapContribution_from_row 0 5 7 6 0 row_00_05_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_06

theorem row_00_05_07_07 : b4RowContribution (![0, 5, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 19^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_07

theorem weighted_00_05_07_07 : b4RawGapContribution ![0, 5, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 7] = b4GapPatternWeight 5 7 7 * 0 :=
      b4GapContribution_from_row 0 5 7 7 0 row_00_05_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_07

theorem row_00_05_07_08 : b4RowContribution (![0, 5, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 12, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 12 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 569 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 12^2 + 20^2 = 569
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_07_08

theorem weighted_00_05_07_08 : b4RawGapContribution ![0, 5, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 7, 8] = b4GapPatternWeight 5 7 8 * 0 :=
      b4GapContribution_from_row 0 5 7 8 0 row_00_05_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_07_08

def dvalues_00_05_07 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_07

theorem dblock_00_05_07 : b4GapPatternDBlock 0 5 7 = 0 := by
  calc
    b4GapPatternDBlock 0 5 7 = ∑ d : Fin 9, dvalues_00_05_07 d := by
      apply b4GapDBlock_of_rows 0 5 7 dvalues_00_05_07
      intro d
      fin_cases d
      · exact weighted_00_05_07_00
      · exact weighted_00_05_07_01
      · exact weighted_00_05_07_02
      · exact weighted_00_05_07_03
      · exact weighted_00_05_07_04
      · exact weighted_00_05_07_05
      · exact weighted_00_05_07_06
      · exact weighted_00_05_07_07
      · exact weighted_00_05_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_07

end Paper7MomentGapNumeric
