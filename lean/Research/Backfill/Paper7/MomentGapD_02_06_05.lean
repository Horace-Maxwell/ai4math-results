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

theorem row_02_06_05_00 : b4RowContribution (![2, 8, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 13, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 13 + 13 = 36
    decide
  have hzsq : (∑ i, (((![2, 8, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 13^2 + 13^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_05_00

theorem weighted_02_06_05_00 : b4RawGapContribution ![2, 6, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 5, 0] = b4GapPatternWeight 6 5 0 * 0 :=
      b4GapContribution_from_row 2 6 5 0 0 row_02_06_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_05_00

theorem row_02_06_05_01 : b4RowContribution (![2, 8, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 13, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 13 + 14 = 37
    decide
  have hzsq : (∑ i, (((![2, 8, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 13^2 + 14^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_05_01

theorem weighted_02_06_05_01 : b4RawGapContribution ![2, 6, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 5, 1] = b4GapPatternWeight 6 5 1 * 0 :=
      b4GapContribution_from_row 2 6 5 1 0 row_02_06_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_05_01

def dvalues_02_06_05 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_06_05

theorem dblock_02_06_05 : b4GapPatternDBlock 2 6 5 = 0 := by
  calc
    b4GapPatternDBlock 2 6 5 = ∑ d : Fin 2, dvalues_02_06_05 d := by
      apply b4GapDBlock_of_rows 2 6 5 dvalues_02_06_05
      intro d
      fin_cases d
      · exact weighted_02_06_05_00
      · exact weighted_02_06_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_06_05

end Paper7MomentGapNumeric
