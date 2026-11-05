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

theorem row_03_00_10_00 : b4RowContribution (![3, 3, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 13 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 13^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_00

theorem weighted_03_00_10_00 : b4RawGapContribution ![3, 0, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 0] = b4GapPatternWeight 0 10 0 * 0 :=
      b4GapContribution_from_row 3 0 10 0 0 row_03_00_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_00

theorem row_03_00_10_01 : b4RowContribution (![3, 3, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 14 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 14^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_01

theorem weighted_03_00_10_01 : b4RawGapContribution ![3, 0, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 1] = b4GapPatternWeight 0 10 1 * 0 :=
      b4GapContribution_from_row 3 0 10 1 0 row_03_00_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_01

theorem row_03_00_10_02 : b4RowContribution (![3, 3, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 15 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 412 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 15^2 = 412
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_02

theorem weighted_03_00_10_02 : b4RawGapContribution ![3, 0, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 2] = b4GapPatternWeight 0 10 2 * 0 :=
      b4GapContribution_from_row 3 0 10 2 0 row_03_00_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_02

theorem row_03_00_10_03 : b4RowContribution (![3, 3, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 16 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 16^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_03

theorem weighted_03_00_10_03 : b4RawGapContribution ![3, 0, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 3] = b4GapPatternWeight 0 10 3 * 0 :=
      b4GapContribution_from_row 3 0 10 3 0 row_03_00_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_03

theorem row_03_00_10_04 : b4RowContribution (![3, 3, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 17 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 476 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 17^2 = 476
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_04

theorem weighted_03_00_10_04 : b4RawGapContribution ![3, 0, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 4] = b4GapPatternWeight 0 10 4 * 0 :=
      b4GapContribution_from_row 3 0 10 4 0 row_03_00_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_04

theorem row_03_00_10_05 : b4RowContribution (![3, 3, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 13, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 13 + 18 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 511 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 13^2 + 18^2 = 511
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_10_05

theorem weighted_03_00_10_05 : b4RawGapContribution ![3, 0, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 10, 5] = b4GapPatternWeight 0 10 5 * 0 :=
      b4GapContribution_from_row 3 0 10 5 0 row_03_00_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_10_05

def dvalues_03_00_10 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_10

theorem dblock_03_00_10 : b4GapPatternDBlock 3 0 10 = 0 := by
  calc
    b4GapPatternDBlock 3 0 10 = ∑ d : Fin 6, dvalues_03_00_10 d := by
      apply b4GapDBlock_of_rows 3 0 10 dvalues_03_00_10
      intro d
      fin_cases d
      · exact weighted_03_00_10_00
      · exact weighted_03_00_10_01
      · exact weighted_03_00_10_02
      · exact weighted_03_00_10_03
      · exact weighted_03_00_10_04
      · exact weighted_03_00_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_10

end Paper7MomentGapNumeric
