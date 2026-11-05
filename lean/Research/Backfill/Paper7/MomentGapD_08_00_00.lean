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

theorem row_08_00_00_00 : b4RowContribution (![8, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 8] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 8 = 32
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 256 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 256
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_00

theorem weighted_08_00_00_00 : b4RawGapContribution ![8, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 8 0 0 0 0 row_08_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_00

theorem row_08_00_00_01 : b4RowContribution (![8, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 9] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 9 = 33
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 273
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_01

theorem weighted_08_00_00_01 : b4RawGapContribution ![8, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 8 0 0 1 0 row_08_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_01

theorem row_08_00_00_02 : b4RowContribution (![8, 8, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 10] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 10 = 34
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_02

theorem weighted_08_00_00_02 : b4RawGapContribution ![8, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 8 0 0 2 0 row_08_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_02

theorem row_08_00_00_03 : b4RowContribution (![8, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 11] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 11 = 35
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_03

theorem weighted_08_00_00_03 : b4RawGapContribution ![8, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 8 0 0 3 0 row_08_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_03

theorem row_08_00_00_04 : b4RowContribution (![8, 8, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 12 = 36
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 336 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 336
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_04

theorem weighted_08_00_00_04 : b4RawGapContribution ![8, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 8 0 0 4 0 row_08_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_04

theorem row_08_00_00_05 : b4RowContribution (![8, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 8, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 8 + 13 = 37
    decide
  have hzsq : (∑ i, (((![8, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_00_05

theorem weighted_08_00_00_05 : b4RawGapContribution ![8, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 8 0 0 5 0 row_08_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_00_05

def dvalues_08_00_00 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_08_00_00

theorem dblock_08_00_00 : b4GapPatternDBlock 8 0 0 = 0 := by
  calc
    b4GapPatternDBlock 8 0 0 = ∑ d : Fin 6, dvalues_08_00_00 d := by
      apply b4GapDBlock_of_rows 8 0 0 dvalues_08_00_00
      intro d
      fin_cases d
      · exact weighted_08_00_00_00
      · exact weighted_08_00_00_01
      · exact weighted_08_00_00_02
      · exact weighted_08_00_00_03
      · exact weighted_08_00_00_04
      · exact weighted_08_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_08_00_00

end Paper7MomentGapNumeric
