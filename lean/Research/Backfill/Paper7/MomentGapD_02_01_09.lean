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

theorem row_02_01_09_00 : b4RowContribution (![2, 3, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 12 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 12^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_00

theorem weighted_02_01_09_00 : b4RawGapContribution ![2, 1, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 0] = b4GapPatternWeight 1 9 0 * 0 :=
      b4GapContribution_from_row 2 1 9 0 0 row_02_01_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_00

theorem row_02_01_09_01 : b4RowContribution (![2, 3, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 13 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 13^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_01

theorem weighted_02_01_09_01 : b4RawGapContribution ![2, 1, 9, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 1] = b4GapPatternWeight 1 9 1 * 0 :=
      b4GapContribution_from_row 2 1 9 1 0 row_02_01_09_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_01

theorem row_02_01_09_02 : b4RowContribution (![2, 3, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 14^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_02

theorem weighted_02_01_09_02 : b4RawGapContribution ![2, 1, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 2] = b4GapPatternWeight 1 9 2 * 0 :=
      b4GapContribution_from_row 2 1 9 2 0 row_02_01_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_02

theorem row_02_01_09_03 : b4RowContribution (![2, 3, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 15^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_03

theorem weighted_02_01_09_03 : b4RawGapContribution ![2, 1, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 3] = b4GapPatternWeight 1 9 3 * 0 :=
      b4GapContribution_from_row 2 1 9 3 0 row_02_01_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_03

theorem row_02_01_09_04 : b4RowContribution (![2, 3, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 16^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_04

theorem weighted_02_01_09_04 : b4RawGapContribution ![2, 1, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 4] = b4GapPatternWeight 1 9 4 * 0 :=
      b4GapContribution_from_row 2 1 9 4 0 row_02_01_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_04

theorem row_02_01_09_05 : b4RowContribution (![2, 3, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 17^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_05

theorem weighted_02_01_09_05 : b4RawGapContribution ![2, 1, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 5] = b4GapPatternWeight 1 9 5 * 0 :=
      b4GapContribution_from_row 2 1 9 5 0 row_02_01_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_05

theorem row_02_01_09_06 : b4RowContribution (![2, 3, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 481 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 18^2 = 481
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_06

theorem weighted_02_01_09_06 : b4RawGapContribution ![2, 1, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 6] = b4GapPatternWeight 1 9 6 * 0 :=
      b4GapContribution_from_row 2 1 9 6 0 row_02_01_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_06

theorem row_02_01_09_07 : b4RowContribution (![2, 3, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 19^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_07

theorem weighted_02_01_09_07 : b4RawGapContribution ![2, 1, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 7] = b4GapPatternWeight 1 9 7 * 0 :=
      b4GapContribution_from_row 2 1 9 7 0 row_02_01_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_07

theorem row_02_01_09_08 : b4RowContribution (![2, 3, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 12, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 12 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 557 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 12^2 + 20^2 = 557
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_09_08

theorem weighted_02_01_09_08 : b4RawGapContribution ![2, 1, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 9, 8] = b4GapPatternWeight 1 9 8 * 0 :=
      b4GapContribution_from_row 2 1 9 8 0 row_02_01_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_09_08

def dvalues_02_01_09 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_09

theorem dblock_02_01_09 : b4GapPatternDBlock 2 1 9 = 0 := by
  calc
    b4GapPatternDBlock 2 1 9 = ∑ d : Fin 9, dvalues_02_01_09 d := by
      apply b4GapDBlock_of_rows 2 1 9 dvalues_02_01_09
      intro d
      fin_cases d
      · exact weighted_02_01_09_00
      · exact weighted_02_01_09_01
      · exact weighted_02_01_09_02
      · exact weighted_02_01_09_03
      · exact weighted_02_01_09_04
      · exact weighted_02_01_09_05
      · exact weighted_02_01_09_06
      · exact weighted_02_01_09_07
      · exact weighted_02_01_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_09

end Paper7MomentGapNumeric
