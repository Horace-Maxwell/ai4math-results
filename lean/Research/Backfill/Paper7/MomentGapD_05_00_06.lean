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

theorem row_05_00_06_00 : b4RowContribution (![5, 5, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 11 = 32
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 11^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_00

theorem weighted_05_00_06_00 : b4RawGapContribution ![5, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 5 0 6 0 0 row_05_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_00

theorem row_05_00_06_01 : b4RowContribution (![5, 5, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 12 = 33
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 12^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_01

theorem weighted_05_00_06_01 : b4RawGapContribution ![5, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 5 0 6 1 0 row_05_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_01

theorem row_05_00_06_02 : b4RowContribution (![5, 5, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 13 = 34
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 13^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_02

theorem weighted_05_00_06_02 : b4RawGapContribution ![5, 0, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 0 :=
      b4GapContribution_from_row 5 0 6 2 0 row_05_00_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_02

theorem row_05_00_06_03 : b4RowContribution (![5, 5, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 14 = 35
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 14^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_03

theorem weighted_05_00_06_03 : b4RawGapContribution ![5, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 5 0 6 3 0 row_05_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_03

theorem row_05_00_06_04 : b4RowContribution (![5, 5, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 15 = 36
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 15^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_04

theorem weighted_05_00_06_04 : b4RawGapContribution ![5, 0, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 0 :=
      b4GapContribution_from_row 5 0 6 4 0 row_05_00_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_04

theorem row_05_00_06_05 : b4RowContribution (![5, 5, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 11, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 11 + 16 = 37
    decide
  have hzsq : (∑ i, (((![5, 5, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 11^2 + 16^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_06_05

theorem weighted_05_00_06_05 : b4RawGapContribution ![5, 0, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 0 :=
      b4GapContribution_from_row 5 0 6 5 0 row_05_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_06_05

def dvalues_05_00_06 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_00_06

theorem dblock_05_00_06 : b4GapPatternDBlock 5 0 6 = 0 := by
  calc
    b4GapPatternDBlock 5 0 6 = ∑ d : Fin 6, dvalues_05_00_06 d := by
      apply b4GapDBlock_of_rows 5 0 6 dvalues_05_00_06
      intro d
      fin_cases d
      · exact weighted_05_00_06_00
      · exact weighted_05_00_06_01
      · exact weighted_05_00_06_02
      · exact weighted_05_00_06_03
      · exact weighted_05_00_06_04
      · exact weighted_05_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_00_06

end Paper7MomentGapNumeric
