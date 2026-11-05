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

theorem row_02_05_06_00 : b4RowContribution (![2, 7, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 13, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 13 + 13 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 13^2 + 13^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_06_00

theorem weighted_02_05_06_00 : b4RawGapContribution ![2, 5, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 6, 0] = b4GapPatternWeight 5 6 0 * 0 :=
      b4GapContribution_from_row 2 5 6 0 0 row_02_05_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_06_00

theorem row_02_05_06_01 : b4RowContribution (![2, 7, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 13, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 13 + 14 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 13^2 + 14^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_06_01

theorem weighted_02_05_06_01 : b4RawGapContribution ![2, 5, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 6, 1] = b4GapPatternWeight 5 6 1 * 0 :=
      b4GapContribution_from_row 2 5 6 1 0 row_02_05_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_06_01

theorem row_02_05_06_02 : b4RowContribution (![2, 7, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 13, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 13 + 15 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 13^2 + 15^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_06_02

theorem weighted_02_05_06_02 : b4RawGapContribution ![2, 5, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 6, 2] = b4GapPatternWeight 5 6 2 * 0 :=
      b4GapContribution_from_row 2 5 6 2 0 row_02_05_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_06_02

def dvalues_02_05_06 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_06

theorem dblock_02_05_06 : b4GapPatternDBlock 2 5 6 = 0 := by
  calc
    b4GapPatternDBlock 2 5 6 = ∑ d : Fin 3, dvalues_02_05_06 d := by
      apply b4GapDBlock_of_rows 2 5 6 dvalues_02_05_06
      intro d
      fin_cases d
      · exact weighted_02_05_06_00
      · exact weighted_02_05_06_01
      · exact weighted_02_05_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_06

end Paper7MomentGapNumeric
