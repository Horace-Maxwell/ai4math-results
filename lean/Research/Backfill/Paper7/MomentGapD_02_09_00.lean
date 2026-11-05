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

theorem row_02_09_00_00 : b4RowContribution (![2, 11, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 11, 11, 11] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 11 + 11 + 11 = 35
    decide
  have hzsq : (∑ i, (((![2, 11, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 11^2 + 11^2 + 11^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_09_00_00

theorem weighted_02_09_00_00 : b4RawGapContribution ![2, 9, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 9, 0, 0] = b4GapPatternWeight 9 0 0 * 0 :=
      b4GapContribution_from_row 2 9 0 0 0 row_02_09_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_09_00_00

theorem row_02_09_00_01 : b4RowContribution (![2, 11, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 11, 11, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 11 + 11 + 12 = 36
    decide
  have hzsq : (∑ i, (((![2, 11, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 11^2 + 11^2 + 12^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_09_00_01

theorem weighted_02_09_00_01 : b4RawGapContribution ![2, 9, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 9, 0, 1] = b4GapPatternWeight 9 0 1 * 0 :=
      b4GapContribution_from_row 2 9 0 1 0 row_02_09_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_09_00_01

theorem row_02_09_00_02 : b4RowContribution (![2, 11, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 11, 11, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 11 + 11 + 13 = 37
    decide
  have hzsq : (∑ i, (((![2, 11, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 11^2 + 11^2 + 13^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_09_00_02

theorem weighted_02_09_00_02 : b4RawGapContribution ![2, 9, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 9, 0, 2] = b4GapPatternWeight 9 0 2 * 0 :=
      b4GapContribution_from_row 2 9 0 2 0 row_02_09_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_09_00_02

def dvalues_02_09_00 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_09_00

theorem dblock_02_09_00 : b4GapPatternDBlock 2 9 0 = 0 := by
  calc
    b4GapPatternDBlock 2 9 0 = ∑ d : Fin 3, dvalues_02_09_00 d := by
      apply b4GapDBlock_of_rows 2 9 0 dvalues_02_09_00
      intro d
      fin_cases d
      · exact weighted_02_09_00_00
      · exact weighted_02_09_00_01
      · exact weighted_02_09_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_09_00

end Paper7MomentGapNumeric
