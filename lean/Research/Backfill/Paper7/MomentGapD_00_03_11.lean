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

theorem row_00_03_11_00 : b4RowContribution (![0, 3, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 14^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_00

theorem weighted_00_03_11_00 : b4RawGapContribution ![0, 3, 11, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 0] = b4GapPatternWeight 3 11 0 * 0 :=
      b4GapContribution_from_row 0 3 11 0 0 row_00_03_11_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_00

theorem row_00_03_11_01 : b4RowContribution (![0, 3, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 15^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_01

theorem weighted_00_03_11_01 : b4RawGapContribution ![0, 3, 11, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 1] = b4GapPatternWeight 3 11 1 * 0 :=
      b4GapContribution_from_row 0 3 11 1 0 row_00_03_11_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_01

theorem row_00_03_11_02 : b4RowContribution (![0, 3, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 16^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_02

theorem weighted_00_03_11_02 : b4RawGapContribution ![0, 3, 11, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 2] = b4GapPatternWeight 3 11 2 * 0 :=
      b4GapContribution_from_row 0 3 11 2 0 row_00_03_11_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_02

theorem row_00_03_11_03 : b4RowContribution (![0, 3, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 17^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_03

theorem weighted_00_03_11_03 : b4RawGapContribution ![0, 3, 11, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 3] = b4GapPatternWeight 3 11 3 * 0 :=
      b4GapContribution_from_row 0 3 11 3 0 row_00_03_11_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_03

theorem row_00_03_11_04 : b4RowContribution (![0, 3, 14, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 18^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_04

theorem weighted_00_03_11_04 : b4RawGapContribution ![0, 3, 11, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 4] = b4GapPatternWeight 3 11 4 * 0 :=
      b4GapContribution_from_row 0 3 11 4 0 row_00_03_11_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_04

theorem row_00_03_11_05 : b4RowContribution (![0, 3, 14, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 19^2 = 566
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_05

theorem weighted_00_03_11_05 : b4RawGapContribution ![0, 3, 11, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 5] = b4GapPatternWeight 3 11 5 * 0 :=
      b4GapContribution_from_row 0 3 11 5 0 row_00_03_11_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_05

theorem row_00_03_11_06 : b4RowContribution (![0, 3, 14, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 14, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 14 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 14, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 605 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 14^2 + 20^2 = 605
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_11_06

theorem weighted_00_03_11_06 : b4RawGapContribution ![0, 3, 11, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 11, 6] = b4GapPatternWeight 3 11 6 * 0 :=
      b4GapContribution_from_row 0 3 11 6 0 row_00_03_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_11_06

def dvalues_00_03_11 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_11

theorem dblock_00_03_11 : b4GapPatternDBlock 0 3 11 = 0 := by
  calc
    b4GapPatternDBlock 0 3 11 = ∑ d : Fin 7, dvalues_00_03_11 d := by
      apply b4GapDBlock_of_rows 0 3 11 dvalues_00_03_11
      intro d
      fin_cases d
      · exact weighted_00_03_11_00
      · exact weighted_00_03_11_01
      · exact weighted_00_03_11_02
      · exact weighted_00_03_11_03
      · exact weighted_00_03_11_04
      · exact weighted_00_03_11_05
      · exact weighted_00_03_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_11

end Paper7MomentGapNumeric
