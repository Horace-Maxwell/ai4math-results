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

theorem row_01_08_04_00 : b4RowContribution (![1, 9, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 13, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 13 + 13 = 36
    decide
  have hzsq : (∑ i, (((![1, 9, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 13^2 + 13^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_04_00

theorem weighted_01_08_04_00 : b4RawGapContribution ![1, 8, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 4, 0] = b4GapPatternWeight 8 4 0 * 0 :=
      b4GapContribution_from_row 1 8 4 0 0 row_01_08_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_04_00

theorem row_01_08_04_01 : b4RowContribution (![1, 9, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 13, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 13 + 14 = 37
    decide
  have hzsq : (∑ i, (((![1, 9, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 13^2 + 14^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_04_01

theorem weighted_01_08_04_01 : b4RawGapContribution ![1, 8, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 4, 1] = b4GapPatternWeight 8 4 1 * 0 :=
      b4GapContribution_from_row 1 8 4 1 0 row_01_08_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_04_01

def dvalues_01_08_04 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_08_04

theorem dblock_01_08_04 : b4GapPatternDBlock 1 8 4 = 0 := by
  calc
    b4GapPatternDBlock 1 8 4 = ∑ d : Fin 2, dvalues_01_08_04 d := by
      apply b4GapDBlock_of_rows 1 8 4 dvalues_01_08_04
      intro d
      fin_cases d
      · exact weighted_01_08_04_00
      · exact weighted_01_08_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_08_04

end Paper7MomentGapNumeric
