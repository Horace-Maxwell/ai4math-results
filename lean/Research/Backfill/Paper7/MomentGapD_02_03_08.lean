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

theorem row_02_03_08_00 : b4RowContribution (![2, 5, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 13, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 13 + 13 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 13^2 + 13^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_08_00

theorem weighted_02_03_08_00 : b4RawGapContribution ![2, 3, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 8, 0] = b4GapPatternWeight 3 8 0 * 0 :=
      b4GapContribution_from_row 2 3 8 0 0 row_02_03_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_08_00

theorem row_02_03_08_01 : b4RowContribution (![2, 5, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 13, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 13 + 14 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 13^2 + 14^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_08_01

theorem weighted_02_03_08_01 : b4RawGapContribution ![2, 3, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 8, 1] = b4GapPatternWeight 3 8 1 * 0 :=
      b4GapContribution_from_row 2 3 8 1 0 row_02_03_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_08_01

theorem row_02_03_08_02 : b4RowContribution (![2, 5, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 13, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 13 + 15 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 13^2 + 15^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_08_02

theorem weighted_02_03_08_02 : b4RawGapContribution ![2, 3, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 8, 2] = b4GapPatternWeight 3 8 2 * 0 :=
      b4GapContribution_from_row 2 3 8 2 0 row_02_03_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_08_02

theorem row_02_03_08_03 : b4RowContribution (![2, 5, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 13, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 13 + 16 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 13^2 + 16^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_08_03

theorem weighted_02_03_08_03 : b4RawGapContribution ![2, 3, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 8, 3] = b4GapPatternWeight 3 8 3 * 0 :=
      b4GapContribution_from_row 2 3 8 3 0 row_02_03_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_08_03

theorem row_02_03_08_04 : b4RowContribution (![2, 5, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 13, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 13 + 17 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 13^2 + 17^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_08_04

theorem weighted_02_03_08_04 : b4RawGapContribution ![2, 3, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 8, 4] = b4GapPatternWeight 3 8 4 * 0 :=
      b4GapContribution_from_row 2 3 8 4 0 row_02_03_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_08_04

def dvalues_02_03_08 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_08

theorem dblock_02_03_08 : b4GapPatternDBlock 2 3 8 = 0 := by
  calc
    b4GapPatternDBlock 2 3 8 = ∑ d : Fin 5, dvalues_02_03_08 d := by
      apply b4GapDBlock_of_rows 2 3 8 dvalues_02_03_08
      intro d
      fin_cases d
      · exact weighted_02_03_08_00
      · exact weighted_02_03_08_01
      · exact weighted_02_03_08_02
      · exact weighted_02_03_08_03
      · exact weighted_02_03_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_08

end Paper7MomentGapNumeric
