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

theorem row_08_01_00_00 : b4RowContribution (![8, 9, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 9, 9, 9] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 8 + 9 + 9 + 9 = 35
    decide
  have hzsq : (∑ i, (((![8, 9, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 9^2 + 9^2 + 9^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_01_00_00

theorem weighted_08_01_00_00 : b4RawGapContribution ![8, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![8, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 8 1 0 0 0 row_08_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_01_00_00

theorem row_08_01_00_01 : b4RowContribution (![8, 9, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 9, 9, 10] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 8 + 9 + 9 + 10 = 36
    decide
  have hzsq : (∑ i, (((![8, 9, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 9^2 + 9^2 + 10^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_01_00_01

theorem weighted_08_01_00_01 : b4RawGapContribution ![8, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![8, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 8 1 0 1 0 row_08_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_01_00_01

theorem row_08_01_00_02 : b4RowContribution (![8, 9, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 9, 9, 11] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 8 + 9 + 9 + 11 = 37
    decide
  have hzsq : (∑ i, (((![8, 9, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 9^2 + 9^2 + 11^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_01_00_02

theorem weighted_08_01_00_02 : b4RawGapContribution ![8, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![8, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 8 1 0 2 0 row_08_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_01_00_02

def dvalues_08_01_00 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_08_01_00

theorem dblock_08_01_00 : b4GapPatternDBlock 8 1 0 = 0 := by
  calc
    b4GapPatternDBlock 8 1 0 = ∑ d : Fin 3, dvalues_08_01_00 d := by
      apply b4GapDBlock_of_rows 8 1 0 dvalues_08_01_00
      intro d
      fin_cases d
      · exact weighted_08_01_00_00
      · exact weighted_08_01_00_01
      · exact weighted_08_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_08_01_00

end Paper7MomentGapNumeric
