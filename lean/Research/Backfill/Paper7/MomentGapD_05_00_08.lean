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

theorem row_05_00_08_00 : b4RowContribution (![5, 5, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 13, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 13 + 13 = 36
    decide
  have hzsq : (∑ i, (((![5, 5, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 13^2 + 13^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_08_00

theorem weighted_05_00_08_00 : b4RawGapContribution ![5, 0, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 0 :=
      b4GapContribution_from_row 5 0 8 0 0 row_05_00_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_08_00

theorem row_05_00_08_01 : b4RowContribution (![5, 5, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 13, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 13 + 14 = 37
    decide
  have hzsq : (∑ i, (((![5, 5, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 13^2 + 14^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_08_01

theorem weighted_05_00_08_01 : b4RawGapContribution ![5, 0, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 0 :=
      b4GapContribution_from_row 5 0 8 1 0 row_05_00_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_08_01

def dvalues_05_00_08 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_00_08

theorem dblock_05_00_08 : b4GapPatternDBlock 5 0 8 = 0 := by
  calc
    b4GapPatternDBlock 5 0 8 = ∑ d : Fin 2, dvalues_05_00_08 d := by
      apply b4GapDBlock_of_rows 5 0 8 dvalues_05_00_08
      intro d
      fin_cases d
      · exact weighted_05_00_08_00
      · exact weighted_05_00_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_00_08

end Paper7MomentGapNumeric
