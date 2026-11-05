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

theorem row_00_06_08_00 : b4RowContribution (![0, 6, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 14, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 14 + 14 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 14^2 + 14^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_08_00

theorem weighted_00_06_08_00 : b4RawGapContribution ![0, 6, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 8, 0] = b4GapPatternWeight 6 8 0 * 0 :=
      b4GapContribution_from_row 0 6 8 0 0 row_00_06_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_08_00

theorem row_00_06_08_01 : b4RowContribution (![0, 6, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 14, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 14 + 15 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 14^2 + 15^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_08_01

theorem weighted_00_06_08_01 : b4RawGapContribution ![0, 6, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 8, 1] = b4GapPatternWeight 6 8 1 * 0 :=
      b4GapContribution_from_row 0 6 8 1 0 row_00_06_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_08_01

theorem row_00_06_08_02 : b4RowContribution (![0, 6, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 14, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 14 + 16 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 488 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 14^2 + 16^2 = 488
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_08_02

theorem weighted_00_06_08_02 : b4RawGapContribution ![0, 6, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 8, 2] = b4GapPatternWeight 6 8 2 * 0 :=
      b4GapContribution_from_row 0 6 8 2 0 row_00_06_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_08_02

theorem row_00_06_08_03 : b4RowContribution (![0, 6, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 14, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 14 + 17 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 521 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 14^2 + 17^2 = 521
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_08_03

theorem weighted_00_06_08_03 : b4RawGapContribution ![0, 6, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 8, 3] = b4GapPatternWeight 6 8 3 * 0 :=
      b4GapContribution_from_row 0 6 8 3 0 row_00_06_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_08_03

def dvalues_00_06_08 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_08

theorem dblock_00_06_08 : b4GapPatternDBlock 0 6 8 = 0 := by
  calc
    b4GapPatternDBlock 0 6 8 = ∑ d : Fin 4, dvalues_00_06_08 d := by
      apply b4GapDBlock_of_rows 0 6 8 dvalues_00_06_08
      intro d
      fin_cases d
      · exact weighted_00_06_08_00
      · exact weighted_00_06_08_01
      · exact weighted_00_06_08_02
      · exact weighted_00_06_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_08

end Paper7MomentGapNumeric
