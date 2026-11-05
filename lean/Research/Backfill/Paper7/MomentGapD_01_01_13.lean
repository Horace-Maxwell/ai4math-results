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

theorem row_01_01_13_00 : b4RowContribution (![1, 2, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 15, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 15 + 15 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 15^2 + 15^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_13_00

theorem weighted_01_01_13_00 : b4RawGapContribution ![1, 1, 13, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 13, 0] = b4GapPatternWeight 1 13 0 * 0 :=
      b4GapContribution_from_row 1 1 13 0 0 row_01_01_13_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_13_00

theorem row_01_01_13_01 : b4RowContribution (![1, 2, 15, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 15, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 15 + 16 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 15, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 15^2 + 16^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_13_01

theorem weighted_01_01_13_01 : b4RawGapContribution ![1, 1, 13, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 13, 1] = b4GapPatternWeight 1 13 1 * 0 :=
      b4GapContribution_from_row 1 1 13 1 0 row_01_01_13_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_13_01

theorem row_01_01_13_02 : b4RowContribution (![1, 2, 15, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 15, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 15 + 17 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 15, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 519 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 15^2 + 17^2 = 519
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_13_02

theorem weighted_01_01_13_02 : b4RawGapContribution ![1, 1, 13, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 13, 2] = b4GapPatternWeight 1 13 2 * 0 :=
      b4GapContribution_from_row 1 1 13 2 0 row_01_01_13_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_13_02

theorem row_01_01_13_03 : b4RowContribution (![1, 2, 15, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 15, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 15 + 18 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 15, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 554 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 15^2 + 18^2 = 554
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_13_03

theorem weighted_01_01_13_03 : b4RawGapContribution ![1, 1, 13, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 13, 3] = b4GapPatternWeight 1 13 3 * 0 :=
      b4GapContribution_from_row 1 1 13 3 0 row_01_01_13_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_13_03

theorem row_01_01_13_04 : b4RowContribution (![1, 2, 15, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 15, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 15 + 19 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 15, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 591 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 15^2 + 19^2 = 591
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_13_04

theorem weighted_01_01_13_04 : b4RawGapContribution ![1, 1, 13, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 13, 4] = b4GapPatternWeight 1 13 4 * 0 :=
      b4GapContribution_from_row 1 1 13 4 0 row_01_01_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_13_04

def dvalues_01_01_13 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_13

theorem dblock_01_01_13 : b4GapPatternDBlock 1 1 13 = 0 := by
  calc
    b4GapPatternDBlock 1 1 13 = ∑ d : Fin 5, dvalues_01_01_13 d := by
      apply b4GapDBlock_of_rows 1 1 13 dvalues_01_01_13
      intro d
      fin_cases d
      · exact weighted_01_01_13_00
      · exact weighted_01_01_13_01
      · exact weighted_01_01_13_02
      · exact weighted_01_01_13_03
      · exact weighted_01_01_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_13

end Paper7MomentGapNumeric
