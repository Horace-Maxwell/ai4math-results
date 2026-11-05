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

theorem row_01_03_08_00 : b4RowContribution (![1, 4, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 12 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 12^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_00

theorem weighted_01_03_08_00 : b4RawGapContribution ![1, 3, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 0] = b4GapPatternWeight 3 8 0 * 0 :=
      b4GapContribution_from_row 1 3 8 0 0 row_01_03_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_00

theorem row_01_03_08_01 : b4RowContribution (![1, 4, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 13^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_01

theorem weighted_01_03_08_01 : b4RawGapContribution ![1, 3, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 1] = b4GapPatternWeight 3 8 1 * 0 :=
      b4GapContribution_from_row 1 3 8 1 0 row_01_03_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_01

theorem row_01_03_08_02 : b4RowContribution (![1, 4, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 14^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_02

theorem weighted_01_03_08_02 : b4RawGapContribution ![1, 3, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 2] = b4GapPatternWeight 3 8 2 * 0 :=
      b4GapContribution_from_row 1 3 8 2 0 row_01_03_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_02

theorem row_01_03_08_03 : b4RowContribution (![1, 4, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 15^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_03

theorem weighted_01_03_08_03 : b4RawGapContribution ![1, 3, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 3] = b4GapPatternWeight 3 8 3 * 0 :=
      b4GapContribution_from_row 1 3 8 3 0 row_01_03_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_03

theorem row_01_03_08_04 : b4RowContribution (![1, 4, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 16^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_04

theorem weighted_01_03_08_04 : b4RawGapContribution ![1, 3, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 4] = b4GapPatternWeight 3 8 4 * 0 :=
      b4GapContribution_from_row 1 3 8 4 0 row_01_03_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_04

theorem row_01_03_08_05 : b4RowContribution (![1, 4, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 17^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_05

theorem weighted_01_03_08_05 : b4RawGapContribution ![1, 3, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 5] = b4GapPatternWeight 3 8 5 * 0 :=
      b4GapContribution_from_row 1 3 8 5 0 row_01_03_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_05

theorem row_01_03_08_06 : b4RowContribution (![1, 4, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 18^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_06

theorem weighted_01_03_08_06 : b4RawGapContribution ![1, 3, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 6] = b4GapPatternWeight 3 8 6 * 0 :=
      b4GapContribution_from_row 1 3 8 6 0 row_01_03_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_06

theorem row_01_03_08_07 : b4RowContribution (![1, 4, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 522 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 19^2 = 522
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_07

theorem weighted_01_03_08_07 : b4RawGapContribution ![1, 3, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 7] = b4GapPatternWeight 3 8 7 * 0 :=
      b4GapContribution_from_row 1 3 8 7 0 row_01_03_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_07

theorem row_01_03_08_08 : b4RowContribution (![1, 4, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 12, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 12 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 561 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 12^2 + 20^2 = 561
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_08_08

theorem weighted_01_03_08_08 : b4RawGapContribution ![1, 3, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 8, 8] = b4GapPatternWeight 3 8 8 * 0 :=
      b4GapContribution_from_row 1 3 8 8 0 row_01_03_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_08_08

def dvalues_01_03_08 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_08

theorem dblock_01_03_08 : b4GapPatternDBlock 1 3 8 = 0 := by
  calc
    b4GapPatternDBlock 1 3 8 = ∑ d : Fin 9, dvalues_01_03_08 d := by
      apply b4GapDBlock_of_rows 1 3 8 dvalues_01_03_08
      intro d
      fin_cases d
      · exact weighted_01_03_08_00
      · exact weighted_01_03_08_01
      · exact weighted_01_03_08_02
      · exact weighted_01_03_08_03
      · exact weighted_01_03_08_04
      · exact weighted_01_03_08_05
      · exact weighted_01_03_08_06
      · exact weighted_01_03_08_07
      · exact weighted_01_03_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_08

end Paper7MomentGapNumeric
