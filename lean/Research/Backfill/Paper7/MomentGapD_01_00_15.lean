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

theorem row_01_00_15_00 : b4RowContribution (![1, 1, 16, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 16, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 16 + 16 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 16, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 514 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 16^2 + 16^2 = 514
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_15_00

theorem weighted_01_00_15_00 : b4RawGapContribution ![1, 0, 15, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 15, 0] = b4GapPatternWeight 0 15 0 * 0 :=
      b4GapContribution_from_row 1 0 15 0 0 row_01_00_15_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_15_00

theorem row_01_00_15_01 : b4RowContribution (![1, 1, 16, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 16, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 16 + 17 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 16, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 16^2 + 17^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_15_01

theorem weighted_01_00_15_01 : b4RawGapContribution ![1, 0, 15, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 15, 1] = b4GapPatternWeight 0 15 1 * 0 :=
      b4GapContribution_from_row 1 0 15 1 0 row_01_00_15_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_15_01

theorem row_01_00_15_02 : b4RowContribution (![1, 1, 16, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 16, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 16 + 18 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 16, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 582 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 16^2 + 18^2 = 582
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_15_02

theorem weighted_01_00_15_02 : b4RawGapContribution ![1, 0, 15, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 15, 2] = b4GapPatternWeight 0 15 2 * 0 :=
      b4GapContribution_from_row 1 0 15 2 0 row_01_00_15_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_15_02

theorem row_01_00_15_03 : b4RowContribution (![1, 1, 16, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 16, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 16 + 19 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 16, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 619 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 16^2 + 19^2 = 619
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_15_03

theorem weighted_01_00_15_03 : b4RawGapContribution ![1, 0, 15, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 15, 3] = b4GapPatternWeight 0 15 3 * 0 :=
      b4GapContribution_from_row 1 0 15 3 0 row_01_00_15_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_15_03

def dvalues_01_00_15 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_15

theorem dblock_01_00_15 : b4GapPatternDBlock 1 0 15 = 0 := by
  calc
    b4GapPatternDBlock 1 0 15 = ∑ d : Fin 4, dvalues_01_00_15 d := by
      apply b4GapDBlock_of_rows 1 0 15 dvalues_01_00_15
      intro d
      fin_cases d
      · exact weighted_01_00_15_00
      · exact weighted_01_00_15_01
      · exact weighted_01_00_15_02
      · exact weighted_01_00_15_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_15

end Paper7MomentGapNumeric
