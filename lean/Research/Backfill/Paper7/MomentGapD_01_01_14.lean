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

theorem row_01_01_14_00 : b4RowContribution (![1, 2, 16, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 16, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 16 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 16, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 16^2 + 16^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_14_00

theorem weighted_01_01_14_00 : b4RawGapContribution ![1, 1, 14, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 14, 0] = b4GapPatternWeight 1 14 0 * 0 :=
      b4GapContribution_from_row 1 1 14 0 0 row_01_01_14_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_14_00

theorem row_01_01_14_01 : b4RowContribution (![1, 2, 16, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 16, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 16 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 16, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 16^2 + 17^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_14_01

theorem weighted_01_01_14_01 : b4RawGapContribution ![1, 1, 14, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 14, 1] = b4GapPatternWeight 1 14 1 * 0 :=
      b4GapContribution_from_row 1 1 14 1 0 row_01_01_14_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_14_01

theorem row_01_01_14_02 : b4RowContribution (![1, 2, 16, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 16, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 16 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 16, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 16^2 + 18^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_14_02

theorem weighted_01_01_14_02 : b4RawGapContribution ![1, 1, 14, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 14, 2] = b4GapPatternWeight 1 14 2 * 0 :=
      b4GapContribution_from_row 1 1 14 2 0 row_01_01_14_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_14_02

def dvalues_01_01_14 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_14

theorem dblock_01_01_14 : b4GapPatternDBlock 1 1 14 = 0 := by
  calc
    b4GapPatternDBlock 1 1 14 = ∑ d : Fin 3, dvalues_01_01_14 d := by
      apply b4GapDBlock_of_rows 1 1 14 dvalues_01_01_14
      intro d
      fin_cases d
      · exact weighted_01_01_14_00
      · exact weighted_01_01_14_01
      · exact weighted_01_01_14_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_14

end Paper7MomentGapNumeric
