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

theorem row_02_08_00_00 : b4RowContribution (![2, 10, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 10] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 10 = 32
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 304 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 10^2 = 304
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_00

theorem weighted_02_08_00_00 : b4RawGapContribution ![2, 8, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 0] = b4GapPatternWeight 8 0 0 * 0 :=
      b4GapContribution_from_row 2 8 0 0 0 row_02_08_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_00

theorem row_02_08_00_01 : b4RowContribution (![2, 10, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 11 = 33
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 11^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_01

theorem weighted_02_08_00_01 : b4RawGapContribution ![2, 8, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 1] = b4GapPatternWeight 8 0 1 * 0 :=
      b4GapContribution_from_row 2 8 0 1 0 row_02_08_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_01

theorem row_02_08_00_02 : b4RowContribution (![2, 10, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 12 = 34
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 12^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_02

theorem weighted_02_08_00_02 : b4RawGapContribution ![2, 8, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 2] = b4GapPatternWeight 8 0 2 * 0 :=
      b4GapContribution_from_row 2 8 0 2 0 row_02_08_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_02

theorem row_02_08_00_03 : b4RowContribution (![2, 10, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 13 = 35
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 13^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_03

theorem weighted_02_08_00_03 : b4RawGapContribution ![2, 8, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 3] = b4GapPatternWeight 8 0 3 * 0 :=
      b4GapContribution_from_row 2 8 0 3 0 row_02_08_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_03

theorem row_02_08_00_04 : b4RowContribution (![2, 10, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 14 = 36
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 14^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_04

theorem weighted_02_08_00_04 : b4RawGapContribution ![2, 8, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 4] = b4GapPatternWeight 8 0 4 * 0 :=
      b4GapContribution_from_row 2 8 0 4 0 row_02_08_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_04

theorem row_02_08_00_05 : b4RowContribution (![2, 10, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 10, 10, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 10 + 10 + 15 = 37
    decide
  have hzsq : (∑ i, (((![2, 10, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 10^2 + 10^2 + 15^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_08_00_05

theorem weighted_02_08_00_05 : b4RawGapContribution ![2, 8, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 8, 0, 5] = b4GapPatternWeight 8 0 5 * 0 :=
      b4GapContribution_from_row 2 8 0 5 0 row_02_08_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_08_00_05

def dvalues_02_08_00 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_08_00

theorem dblock_02_08_00 : b4GapPatternDBlock 2 8 0 = 0 := by
  calc
    b4GapPatternDBlock 2 8 0 = ∑ d : Fin 6, dvalues_02_08_00 d := by
      apply b4GapDBlock_of_rows 2 8 0 dvalues_02_08_00
      intro d
      fin_cases d
      · exact weighted_02_08_00_00
      · exact weighted_02_08_00_01
      · exact weighted_02_08_00_02
      · exact weighted_02_08_00_03
      · exact weighted_02_08_00_04
      · exact weighted_02_08_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_08_00

end Paper7MomentGapNumeric
