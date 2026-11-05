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

theorem row_01_04_08_00 : b4RowContribution (![1, 5, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 13 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 13^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_00

theorem weighted_01_04_08_00 : b4RawGapContribution ![1, 4, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 0] = b4GapPatternWeight 4 8 0 * 0 :=
      b4GapContribution_from_row 1 4 8 0 0 row_01_04_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_00

theorem row_01_04_08_01 : b4RowContribution (![1, 5, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 14 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 14^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_01

theorem weighted_01_04_08_01 : b4RawGapContribution ![1, 4, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 1] = b4GapPatternWeight 4 8 1 * 0 :=
      b4GapContribution_from_row 1 4 8 1 0 row_01_04_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_01

theorem row_01_04_08_02 : b4RowContribution (![1, 5, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 15 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 15^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_02

theorem weighted_01_04_08_02 : b4RawGapContribution ![1, 4, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 2] = b4GapPatternWeight 4 8 2 * 0 :=
      b4GapContribution_from_row 1 4 8 2 0 row_01_04_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_02

theorem row_01_04_08_03 : b4RowContribution (![1, 5, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 16^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_03

theorem weighted_01_04_08_03 : b4RawGapContribution ![1, 4, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 3] = b4GapPatternWeight 4 8 3 * 0 :=
      b4GapContribution_from_row 1 4 8 3 0 row_01_04_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_03

theorem row_01_04_08_04 : b4RowContribution (![1, 5, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 484 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 17^2 = 484
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_04

theorem weighted_01_04_08_04 : b4RawGapContribution ![1, 4, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 4] = b4GapPatternWeight 4 8 4 * 0 :=
      b4GapContribution_from_row 1 4 8 4 0 row_01_04_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_04

theorem row_01_04_08_05 : b4RowContribution (![1, 5, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 13, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 13 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 519 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 13^2 + 18^2 = 519
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_08_05

theorem weighted_01_04_08_05 : b4RawGapContribution ![1, 4, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 8, 5] = b4GapPatternWeight 4 8 5 * 0 :=
      b4GapContribution_from_row 1 4 8 5 0 row_01_04_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_08_05

def dvalues_01_04_08 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_08

theorem dblock_01_04_08 : b4GapPatternDBlock 1 4 8 = 0 := by
  calc
    b4GapPatternDBlock 1 4 8 = ∑ d : Fin 6, dvalues_01_04_08 d := by
      apply b4GapDBlock_of_rows 1 4 8 dvalues_01_04_08
      intro d
      fin_cases d
      · exact weighted_01_04_08_00
      · exact weighted_01_04_08_01
      · exact weighted_01_04_08_02
      · exact weighted_01_04_08_03
      · exact weighted_01_04_08_04
      · exact weighted_01_04_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_08

end Paper7MomentGapNumeric
