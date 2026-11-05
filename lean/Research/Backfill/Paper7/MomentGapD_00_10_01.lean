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

theorem row_00_10_01_00 : b4RowContribution (![0, 10, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 11 = 32
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 11^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_00

theorem weighted_00_10_01_00 : b4RawGapContribution ![0, 10, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 0] = b4GapPatternWeight 10 1 0 * 0 :=
      b4GapContribution_from_row 0 10 1 0 0 row_00_10_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_00

theorem row_00_10_01_01 : b4RowContribution (![0, 10, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 12 = 33
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 12^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_01

theorem weighted_00_10_01_01 : b4RawGapContribution ![0, 10, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 1] = b4GapPatternWeight 10 1 1 * 0 :=
      b4GapContribution_from_row 0 10 1 1 0 row_00_10_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_01

theorem row_00_10_01_02 : b4RowContribution (![0, 10, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 13 = 34
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 13^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_02

theorem weighted_00_10_01_02 : b4RawGapContribution ![0, 10, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 2] = b4GapPatternWeight 10 1 2 * 0 :=
      b4GapContribution_from_row 0 10 1 2 0 row_00_10_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_02

theorem row_00_10_01_03 : b4RowContribution (![0, 10, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 14 = 35
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 14^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_03

theorem weighted_00_10_01_03 : b4RawGapContribution ![0, 10, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 3] = b4GapPatternWeight 10 1 3 * 0 :=
      b4GapContribution_from_row 0 10 1 3 0 row_00_10_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_03

theorem row_00_10_01_04 : b4RowContribution (![0, 10, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 15 = 36
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 15^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_04

theorem weighted_00_10_01_04 : b4RawGapContribution ![0, 10, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 4] = b4GapPatternWeight 10 1 4 * 0 :=
      b4GapContribution_from_row 0 10 1 4 0 row_00_10_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_04

theorem row_00_10_01_05 : b4RowContribution (![0, 10, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 11, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 11 + 16 = 37
    decide
  have hzsq : (∑ i, (((![0, 10, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 11^2 + 16^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_01_05

theorem weighted_00_10_01_05 : b4RawGapContribution ![0, 10, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 1, 5] = b4GapPatternWeight 10 1 5 * 0 :=
      b4GapContribution_from_row 0 10 1 5 0 row_00_10_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_01_05

def dvalues_00_10_01 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_10_01

theorem dblock_00_10_01 : b4GapPatternDBlock 0 10 1 = 0 := by
  calc
    b4GapPatternDBlock 0 10 1 = ∑ d : Fin 6, dvalues_00_10_01 d := by
      apply b4GapDBlock_of_rows 0 10 1 dvalues_00_10_01
      intro d
      fin_cases d
      · exact weighted_00_10_01_00
      · exact weighted_00_10_01_01
      · exact weighted_00_10_01_02
      · exact weighted_00_10_01_03
      · exact weighted_00_10_01_04
      · exact weighted_00_10_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_10_01

end Paper7MomentGapNumeric
