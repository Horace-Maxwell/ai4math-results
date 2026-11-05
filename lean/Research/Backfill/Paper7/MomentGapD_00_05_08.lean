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

theorem row_00_05_08_00 : b4RowContribution (![0, 5, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 13 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 13^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_00

theorem weighted_00_05_08_00 : b4RawGapContribution ![0, 5, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 0] = b4GapPatternWeight 5 8 0 * 0 :=
      b4GapContribution_from_row 0 5 8 0 0 row_00_05_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_00

theorem row_00_05_08_01 : b4RowContribution (![0, 5, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 14 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 14^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_01

theorem weighted_00_05_08_01 : b4RawGapContribution ![0, 5, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 1] = b4GapPatternWeight 5 8 1 * 0 :=
      b4GapContribution_from_row 0 5 8 1 0 row_00_05_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_01

theorem row_00_05_08_02 : b4RowContribution (![0, 5, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 15 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 15^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_02

theorem weighted_00_05_08_02 : b4RawGapContribution ![0, 5, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 2] = b4GapPatternWeight 5 8 2 * 0 :=
      b4GapContribution_from_row 0 5 8 2 0 row_00_05_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_02

theorem row_00_05_08_03 : b4RowContribution (![0, 5, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 16 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 16^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_03

theorem weighted_00_05_08_03 : b4RawGapContribution ![0, 5, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 3] = b4GapPatternWeight 5 8 3 * 0 :=
      b4GapContribution_from_row 0 5 8 3 0 row_00_05_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_03

theorem row_00_05_08_04 : b4RowContribution (![0, 5, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 17 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 17^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_04

theorem weighted_00_05_08_04 : b4RawGapContribution ![0, 5, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 4] = b4GapPatternWeight 5 8 4 * 0 :=
      b4GapContribution_from_row 0 5 8 4 0 row_00_05_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_04

theorem row_00_05_08_05 : b4RowContribution (![0, 5, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 18 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 18^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_05

theorem weighted_00_05_08_05 : b4RawGapContribution ![0, 5, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 5] = b4GapPatternWeight 5 8 5 * 0 :=
      b4GapContribution_from_row 0 5 8 5 0 row_00_05_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_05

theorem row_00_05_08_06 : b4RowContribution (![0, 5, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 13, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 13 + 19 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 555 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 13^2 + 19^2 = 555
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_08_06

theorem weighted_00_05_08_06 : b4RawGapContribution ![0, 5, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 8, 6] = b4GapPatternWeight 5 8 6 * 0 :=
      b4GapContribution_from_row 0 5 8 6 0 row_00_05_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_08_06

def dvalues_00_05_08 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_08

theorem dblock_00_05_08 : b4GapPatternDBlock 0 5 8 = 0 := by
  calc
    b4GapPatternDBlock 0 5 8 = ∑ d : Fin 7, dvalues_00_05_08 d := by
      apply b4GapDBlock_of_rows 0 5 8 dvalues_00_05_08
      intro d
      fin_cases d
      · exact weighted_00_05_08_00
      · exact weighted_00_05_08_01
      · exact weighted_00_05_08_02
      · exact weighted_00_05_08_03
      · exact weighted_00_05_08_04
      · exact weighted_00_05_08_05
      · exact weighted_00_05_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_08

end Paper7MomentGapNumeric
