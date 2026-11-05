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

theorem row_01_00_13_00 : b4RowContribution (![1, 1, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 14 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 14^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_00

theorem weighted_01_00_13_00 : b4RawGapContribution ![1, 0, 13, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 0] = b4GapPatternWeight 0 13 0 * 0 :=
      b4GapContribution_from_row 1 0 13 0 0 row_01_00_13_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_00

theorem row_01_00_13_01 : b4RowContribution (![1, 1, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 15 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 15^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_01

theorem weighted_01_00_13_01 : b4RawGapContribution ![1, 0, 13, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 1] = b4GapPatternWeight 0 13 1 * 0 :=
      b4GapContribution_from_row 1 0 13 1 0 row_01_00_13_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_01

theorem row_01_00_13_02 : b4RowContribution (![1, 1, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 16 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 16^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_02

theorem weighted_01_00_13_02 : b4RawGapContribution ![1, 0, 13, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 2] = b4GapPatternWeight 0 13 2 * 0 :=
      b4GapContribution_from_row 1 0 13 2 0 row_01_00_13_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_02

theorem row_01_00_13_03 : b4RowContribution (![1, 1, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 17 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 17^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_03

theorem weighted_01_00_13_03 : b4RawGapContribution ![1, 0, 13, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 3] = b4GapPatternWeight 0 13 3 * 0 :=
      b4GapContribution_from_row 1 0 13 3 0 row_01_00_13_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_03

theorem row_01_00_13_04 : b4RowContribution (![1, 1, 14, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 18 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 522 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 18^2 = 522
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_04

theorem weighted_01_00_13_04 : b4RawGapContribution ![1, 0, 13, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 4] = b4GapPatternWeight 0 13 4 * 0 :=
      b4GapContribution_from_row 1 0 13 4 0 row_01_00_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_04

theorem row_01_00_13_05 : b4RowContribution (![1, 1, 14, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 19 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 559 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 19^2 = 559
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_05

theorem weighted_01_00_13_05 : b4RawGapContribution ![1, 0, 13, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 5] = b4GapPatternWeight 0 13 5 * 0 :=
      b4GapContribution_from_row 1 0 13 5 0 row_01_00_13_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_05

theorem row_01_00_13_06 : b4RowContribution (![1, 1, 14, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 20 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 598 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 20^2 = 598
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_06

theorem weighted_01_00_13_06 : b4RawGapContribution ![1, 0, 13, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 6] = b4GapPatternWeight 0 13 6 * 0 :=
      b4GapContribution_from_row 1 0 13 6 0 row_01_00_13_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_06

theorem row_01_00_13_07 : b4RowContribution (![1, 1, 14, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 14, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 14 + 21 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 14, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 639 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 14^2 + 21^2 = 639
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_13_07

theorem weighted_01_00_13_07 : b4RawGapContribution ![1, 0, 13, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 13, 7] = b4GapPatternWeight 0 13 7 * 0 :=
      b4GapContribution_from_row 1 0 13 7 0 row_01_00_13_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_13_07

def dvalues_01_00_13 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_13

theorem dblock_01_00_13 : b4GapPatternDBlock 1 0 13 = 0 := by
  calc
    b4GapPatternDBlock 1 0 13 = ∑ d : Fin 8, dvalues_01_00_13 d := by
      apply b4GapDBlock_of_rows 1 0 13 dvalues_01_00_13
      intro d
      fin_cases d
      · exact weighted_01_00_13_00
      · exact weighted_01_00_13_01
      · exact weighted_01_00_13_02
      · exact weighted_01_00_13_03
      · exact weighted_01_00_13_04
      · exact weighted_01_00_13_05
      · exact weighted_01_00_13_06
      · exact weighted_01_00_13_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_13

end Paper7MomentGapNumeric
