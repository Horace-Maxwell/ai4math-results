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

theorem row_02_07_03_00 : b4RowContribution (![2, 9, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 12, 12] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 12 + 12 = 35
    decide
  have hzsq : (∑ i, (((![2, 9, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 12^2 + 12^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_03_00

theorem weighted_02_07_03_00 : b4RawGapContribution ![2, 7, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 3, 0] = b4GapPatternWeight 7 3 0 * 0 :=
      b4GapContribution_from_row 2 7 3 0 0 row_02_07_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_03_00

theorem row_02_07_03_01 : b4RowContribution (![2, 9, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 12, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 12 + 13 = 36
    decide
  have hzsq : (∑ i, (((![2, 9, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 12^2 + 13^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_03_01

theorem weighted_02_07_03_01 : b4RawGapContribution ![2, 7, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 3, 1] = b4GapPatternWeight 7 3 1 * 0 :=
      b4GapContribution_from_row 2 7 3 1 0 row_02_07_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_03_01

theorem row_02_07_03_02 : b4RowContribution (![2, 9, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 12, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 12 + 14 = 37
    decide
  have hzsq : (∑ i, (((![2, 9, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 12^2 + 14^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_03_02

theorem weighted_02_07_03_02 : b4RawGapContribution ![2, 7, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 3, 2] = b4GapPatternWeight 7 3 2 * 0 :=
      b4GapContribution_from_row 2 7 3 2 0 row_02_07_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_03_02

def dvalues_02_07_03 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_07_03

theorem dblock_02_07_03 : b4GapPatternDBlock 2 7 3 = 0 := by
  calc
    b4GapPatternDBlock 2 7 3 = ∑ d : Fin 3, dvalues_02_07_03 d := by
      apply b4GapDBlock_of_rows 2 7 3 dvalues_02_07_03
      intro d
      fin_cases d
      · exact weighted_02_07_03_00
      · exact weighted_02_07_03_01
      · exact weighted_02_07_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_07_03

end Paper7MomentGapNumeric
