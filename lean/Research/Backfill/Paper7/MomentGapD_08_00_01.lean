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

theorem row_08_00_01_00 : b4RowContribution (![8, 8, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 9, 9] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 9 + 9 = 34
    decide
  have hzsq : (∑ i, (((![8, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_01_00

theorem weighted_08_00_01_00 : b4RawGapContribution ![8, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 8 0 1 0 0 row_08_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_01_00

theorem row_08_00_01_01 : b4RowContribution (![8, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 9, 10] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 9 + 10 = 35
    decide
  have hzsq : (∑ i, (((![8, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_01_01

theorem weighted_08_00_01_01 : b4RawGapContribution ![8, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 8 0 1 1 0 row_08_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_01_01

theorem row_08_00_01_02 : b4RowContribution (![8, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 9, 11] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 9 + 11 = 36
    decide
  have hzsq : (∑ i, (((![8, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_01_02

theorem weighted_08_00_01_02 : b4RawGapContribution ![8, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 8 0 1 2 0 row_08_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_01_02

theorem row_08_00_01_03 : b4RowContribution (![8, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 9, 12] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 9 + 12 = 37
    decide
  have hzsq : (∑ i, (((![8, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_01_03

theorem weighted_08_00_01_03 : b4RawGapContribution ![8, 0, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 0 :=
      b4GapContribution_from_row 8 0 1 3 0 row_08_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_01_03

def dvalues_08_00_01 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_08_00_01

theorem dblock_08_00_01 : b4GapPatternDBlock 8 0 1 = 0 := by
  calc
    b4GapPatternDBlock 8 0 1 = ∑ d : Fin 4, dvalues_08_00_01 d := by
      apply b4GapDBlock_of_rows 8 0 1 dvalues_08_00_01
      intro d
      fin_cases d
      · exact weighted_08_00_01_00
      · exact weighted_08_00_01_01
      · exact weighted_08_00_01_02
      · exact weighted_08_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_08_00_01

end Paper7MomentGapNumeric
