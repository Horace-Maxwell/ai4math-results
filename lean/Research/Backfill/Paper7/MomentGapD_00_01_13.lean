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

theorem row_00_01_13_00 : b4RowContribution (![0, 1, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 14^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_00

theorem weighted_00_01_13_00 : b4RawGapContribution ![0, 1, 13, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 0] = b4GapPatternWeight 1 13 0 * 0 :=
      b4GapContribution_from_row 0 1 13 0 0 row_00_01_13_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_00

theorem row_00_01_13_01 : b4RowContribution (![0, 1, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 15^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_01

theorem weighted_00_01_13_01 : b4RawGapContribution ![0, 1, 13, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 1] = b4GapPatternWeight 1 13 1 * 0 :=
      b4GapContribution_from_row 0 1 13 1 0 row_00_01_13_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_01

theorem row_00_01_13_02 : b4RowContribution (![0, 1, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 16^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_02

theorem weighted_00_01_13_02 : b4RawGapContribution ![0, 1, 13, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 2] = b4GapPatternWeight 1 13 2 * 0 :=
      b4GapContribution_from_row 0 1 13 2 0 row_00_01_13_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_02

theorem row_00_01_13_03 : b4RowContribution (![0, 1, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 17^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_03

theorem weighted_00_01_13_03 : b4RawGapContribution ![0, 1, 13, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 3] = b4GapPatternWeight 1 13 3 * 0 :=
      b4GapContribution_from_row 0 1 13 3 0 row_00_01_13_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_03

theorem row_00_01_13_04 : b4RowContribution (![0, 1, 14, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 521 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 18^2 = 521
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_04

theorem weighted_00_01_13_04 : b4RawGapContribution ![0, 1, 13, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 4] = b4GapPatternWeight 1 13 4 * 0 :=
      b4GapContribution_from_row 0 1 13 4 0 row_00_01_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_04

theorem row_00_01_13_05 : b4RowContribution (![0, 1, 14, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 19^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_05

theorem weighted_00_01_13_05 : b4RawGapContribution ![0, 1, 13, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 5] = b4GapPatternWeight 1 13 5 * 0 :=
      b4GapContribution_from_row 0 1 13 5 0 row_00_01_13_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_05

theorem row_00_01_13_06 : b4RowContribution (![0, 1, 14, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 597 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 20^2 = 597
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_06

theorem weighted_00_01_13_06 : b4RawGapContribution ![0, 1, 13, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 6] = b4GapPatternWeight 1 13 6 * 0 :=
      b4GapContribution_from_row 0 1 13 6 0 row_00_01_13_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_06

theorem row_00_01_13_07 : b4RowContribution (![0, 1, 14, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 638 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 21^2 = 638
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_07

theorem weighted_00_01_13_07 : b4RawGapContribution ![0, 1, 13, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 7] = b4GapPatternWeight 1 13 7 * 0 :=
      b4GapContribution_from_row 0 1 13 7 0 row_00_01_13_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_07

theorem row_00_01_13_08 : b4RowContribution (![0, 1, 14, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 14, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 14 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 14, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 681 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 14^2 + 22^2 = 681
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_13_08

theorem weighted_00_01_13_08 : b4RawGapContribution ![0, 1, 13, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 13, 8] = b4GapPatternWeight 1 13 8 * 0 :=
      b4GapContribution_from_row 0 1 13 8 0 row_00_01_13_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_13_08

def dvalues_00_01_13 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_13

theorem dblock_00_01_13 : b4GapPatternDBlock 0 1 13 = 0 := by
  calc
    b4GapPatternDBlock 0 1 13 = ∑ d : Fin 9, dvalues_00_01_13 d := by
      apply b4GapDBlock_of_rows 0 1 13 dvalues_00_01_13
      intro d
      fin_cases d
      · exact weighted_00_01_13_00
      · exact weighted_00_01_13_01
      · exact weighted_00_01_13_02
      · exact weighted_00_01_13_03
      · exact weighted_00_01_13_04
      · exact weighted_00_01_13_05
      · exact weighted_00_01_13_06
      · exact weighted_00_01_13_07
      · exact weighted_00_01_13_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_13

end Paper7MomentGapNumeric
