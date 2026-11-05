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

theorem row_00_10_02_00 : b4RowContribution (![0, 10, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 12, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 12 + 12 = 34
    decide
  have hzsq : (∑ i, (((![0, 10, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 12^2 + 12^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_02_00

theorem weighted_00_10_02_00 : b4RawGapContribution ![0, 10, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 2, 0] = b4GapPatternWeight 10 2 0 * 0 :=
      b4GapContribution_from_row 0 10 2 0 0 row_00_10_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_02_00

theorem row_00_10_02_01 : b4RowContribution (![0, 10, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 12, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 12 + 13 = 35
    decide
  have hzsq : (∑ i, (((![0, 10, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 12^2 + 13^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_02_01

theorem weighted_00_10_02_01 : b4RawGapContribution ![0, 10, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 2, 1] = b4GapPatternWeight 10 2 1 * 0 :=
      b4GapContribution_from_row 0 10 2 1 0 row_00_10_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_02_01

theorem row_00_10_02_02 : b4RowContribution (![0, 10, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 12, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 12 + 14 = 36
    decide
  have hzsq : (∑ i, (((![0, 10, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 440 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 12^2 + 14^2 = 440
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_02_02

theorem weighted_00_10_02_02 : b4RawGapContribution ![0, 10, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 2, 2] = b4GapPatternWeight 10 2 2 * 0 :=
      b4GapContribution_from_row 0 10 2 2 0 row_00_10_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_02_02

theorem row_00_10_02_03 : b4RowContribution (![0, 10, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 10, 12, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 10 + 12 + 15 = 37
    decide
  have hzsq : (∑ i, (((![0, 10, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 10^2 + 12^2 + 15^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_10_02_03

theorem weighted_00_10_02_03 : b4RawGapContribution ![0, 10, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 10, 2, 3] = b4GapPatternWeight 10 2 3 * 0 :=
      b4GapContribution_from_row 0 10 2 3 0 row_00_10_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_10_02_03

def dvalues_00_10_02 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_10_02

theorem dblock_00_10_02 : b4GapPatternDBlock 0 10 2 = 0 := by
  calc
    b4GapPatternDBlock 0 10 2 = ∑ d : Fin 4, dvalues_00_10_02 d := by
      apply b4GapDBlock_of_rows 0 10 2 dvalues_00_10_02
      intro d
      fin_cases d
      · exact weighted_00_10_02_00
      · exact weighted_00_10_02_01
      · exact weighted_00_10_02_02
      · exact weighted_00_10_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_10_02

end Paper7MomentGapNumeric
