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

theorem row_04_02_07_00 : b4RowContribution (![4, 6, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 13, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 13 + 13 = 36
    decide
  have hzsq : (∑ i, (((![4, 6, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 13^2 + 13^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_07_00

theorem weighted_04_02_07_00 : b4RawGapContribution ![4, 2, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 7, 0] = b4GapPatternWeight 2 7 0 * 0 :=
      b4GapContribution_from_row 4 2 7 0 0 row_04_02_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_07_00

theorem row_04_02_07_01 : b4RowContribution (![4, 6, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 13, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 13 + 14 = 37
    decide
  have hzsq : (∑ i, (((![4, 6, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 13^2 + 14^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_07_01

theorem weighted_04_02_07_01 : b4RawGapContribution ![4, 2, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 7, 1] = b4GapPatternWeight 2 7 1 * 0 :=
      b4GapContribution_from_row 4 2 7 1 0 row_04_02_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_07_01

def dvalues_04_02_07 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_02_07

theorem dblock_04_02_07 : b4GapPatternDBlock 4 2 7 = 0 := by
  calc
    b4GapPatternDBlock 4 2 7 = ∑ d : Fin 2, dvalues_04_02_07 d := by
      apply b4GapDBlock_of_rows 4 2 7 dvalues_04_02_07
      intro d
      fin_cases d
      · exact weighted_04_02_07_00
      · exact weighted_04_02_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_02_07

end Paper7MomentGapNumeric
