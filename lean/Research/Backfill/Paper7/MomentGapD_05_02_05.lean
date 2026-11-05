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

theorem row_05_02_05_00 : b4RowContribution (![5, 7, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 12, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 12 + 12 = 36
    decide
  have hzsq : (∑ i, (((![5, 7, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 12^2 + 12^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_05_00

theorem weighted_05_02_05_00 : b4RawGapContribution ![5, 2, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 5, 0] = b4GapPatternWeight 2 5 0 * 0 :=
      b4GapContribution_from_row 5 2 5 0 0 row_05_02_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_05_00

theorem row_05_02_05_01 : b4RowContribution (![5, 7, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 12, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 12 + 13 = 37
    decide
  have hzsq : (∑ i, (((![5, 7, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 12^2 + 13^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_05_01

theorem weighted_05_02_05_01 : b4RawGapContribution ![5, 2, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 5, 1] = b4GapPatternWeight 2 5 1 * 0 :=
      b4GapContribution_from_row 5 2 5 1 0 row_05_02_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_05_01

def dvalues_05_02_05 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_02_05

theorem dblock_05_02_05 : b4GapPatternDBlock 5 2 5 = 0 := by
  calc
    b4GapPatternDBlock 5 2 5 = ∑ d : Fin 2, dvalues_05_02_05 d := by
      apply b4GapDBlock_of_rows 5 2 5 dvalues_05_02_05
      intro d
      fin_cases d
      · exact weighted_05_02_05_00
      · exact weighted_05_02_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_02_05

end Paper7MomentGapNumeric
