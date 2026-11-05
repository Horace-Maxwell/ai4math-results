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

theorem row_05_00_05_00 : b4RowContribution (![5, 5, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 10 = 30
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 10^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_00

theorem weighted_05_00_05_00 : b4RawGapContribution ![5, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 5 0 5 0 0 row_05_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_00

theorem row_05_00_05_01 : b4RowContribution (![5, 5, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 11 = 31
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 11^2 = 271
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_01

theorem weighted_05_00_05_01 : b4RawGapContribution ![5, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 5 0 5 1 0 row_05_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_01

theorem row_05_00_05_02 : b4RowContribution (![5, 5, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 12 = 32
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 12^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_02

theorem weighted_05_00_05_02 : b4RawGapContribution ![5, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 5 0 5 2 0 row_05_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_02

theorem row_05_00_05_03 : b4RowContribution (![5, 5, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 13 = 33
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 13^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_03

theorem weighted_05_00_05_03 : b4RawGapContribution ![5, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 5 0 5 3 0 row_05_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_03

theorem row_05_00_05_04 : b4RowContribution (![5, 5, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 14 = 34
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 14^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_04

theorem weighted_05_00_05_04 : b4RawGapContribution ![5, 0, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 0 :=
      b4GapContribution_from_row 5 0 5 4 0 row_05_00_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_04

theorem row_05_00_05_05 : b4RowContribution (![5, 5, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 15 = 35
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 15^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_05

theorem weighted_05_00_05_05 : b4RawGapContribution ![5, 0, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 0 :=
      b4GapContribution_from_row 5 0 5 5 0 row_05_00_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_05

theorem row_05_00_05_06 : b4RowContribution (![5, 5, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 16 = 36
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 16^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_06

theorem weighted_05_00_05_06 : b4RawGapContribution ![5, 0, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 0 :=
      b4GapContribution_from_row 5 0 5 6 0 row_05_00_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_06

theorem row_05_00_05_07 : b4RowContribution (![5, 5, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 10, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 10 + 17 = 37
    decide
  have hzsq : (∑ i, (((![5, 5, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 439 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 10^2 + 17^2 = 439
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_05_07

theorem weighted_05_00_05_07 : b4RawGapContribution ![5, 0, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 0 :=
      b4GapContribution_from_row 5 0 5 7 0 row_05_00_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_05_07

def dvalues_05_00_05 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_00_05

theorem dblock_05_00_05 : b4GapPatternDBlock 5 0 5 = 0 := by
  calc
    b4GapPatternDBlock 5 0 5 = ∑ d : Fin 8, dvalues_05_00_05 d := by
      apply b4GapDBlock_of_rows 5 0 5 dvalues_05_00_05
      intro d
      fin_cases d
      · exact weighted_05_00_05_00
      · exact weighted_05_00_05_01
      · exact weighted_05_00_05_02
      · exact weighted_05_00_05_03
      · exact weighted_05_00_05_04
      · exact weighted_05_00_05_05
      · exact weighted_05_00_05_06
      · exact weighted_05_00_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_00_05

end Paper7MomentGapNumeric
