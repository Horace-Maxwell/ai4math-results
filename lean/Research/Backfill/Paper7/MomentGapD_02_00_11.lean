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

theorem row_02_00_11_00 : b4RowContribution (![2, 2, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 13 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 13^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_00

theorem weighted_02_00_11_00 : b4RawGapContribution ![2, 0, 11, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 0] = b4GapPatternWeight 0 11 0 * 0 :=
      b4GapContribution_from_row 2 0 11 0 0 row_02_00_11_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_00

theorem row_02_00_11_01 : b4RowContribution (![2, 2, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 14^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_01

theorem weighted_02_00_11_01 : b4RawGapContribution ![2, 0, 11, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 1] = b4GapPatternWeight 0 11 1 * 0 :=
      b4GapContribution_from_row 2 0 11 1 0 row_02_00_11_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_01

theorem row_02_00_11_02 : b4RowContribution (![2, 2, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 15^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_02

theorem weighted_02_00_11_02 : b4RawGapContribution ![2, 0, 11, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 2] = b4GapPatternWeight 0 11 2 * 0 :=
      b4GapContribution_from_row 2 0 11 2 0 row_02_00_11_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_02

theorem row_02_00_11_03 : b4RowContribution (![2, 2, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 16^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_03

theorem weighted_02_00_11_03 : b4RawGapContribution ![2, 0, 11, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 3] = b4GapPatternWeight 0 11 3 * 0 :=
      b4GapContribution_from_row 2 0 11 3 0 row_02_00_11_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_03

theorem row_02_00_11_04 : b4RowContribution (![2, 2, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 466 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 17^2 = 466
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_04

theorem weighted_02_00_11_04 : b4RawGapContribution ![2, 0, 11, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 4] = b4GapPatternWeight 0 11 4 * 0 :=
      b4GapContribution_from_row 2 0 11 4 0 row_02_00_11_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_04

theorem row_02_00_11_05 : b4RowContribution (![2, 2, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 18^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_05

theorem weighted_02_00_11_05 : b4RawGapContribution ![2, 0, 11, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 5] = b4GapPatternWeight 0 11 5 * 0 :=
      b4GapContribution_from_row 2 0 11 5 0 row_02_00_11_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_05

theorem row_02_00_11_06 : b4RowContribution (![2, 2, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 538 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 19^2 = 538
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_06

theorem weighted_02_00_11_06 : b4RawGapContribution ![2, 0, 11, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 6] = b4GapPatternWeight 0 11 6 * 0 :=
      b4GapContribution_from_row 2 0 11 6 0 row_02_00_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_06

theorem row_02_00_11_07 : b4RowContribution (![2, 2, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 13, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 13 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 577 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 13^2 + 20^2 = 577
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_11_07

theorem weighted_02_00_11_07 : b4RawGapContribution ![2, 0, 11, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 11, 7] = b4GapPatternWeight 0 11 7 * 0 :=
      b4GapContribution_from_row 2 0 11 7 0 row_02_00_11_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_11_07

def dvalues_02_00_11 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_11

theorem dblock_02_00_11 : b4GapPatternDBlock 2 0 11 = 0 := by
  calc
    b4GapPatternDBlock 2 0 11 = ∑ d : Fin 8, dvalues_02_00_11 d := by
      apply b4GapDBlock_of_rows 2 0 11 dvalues_02_00_11
      intro d
      fin_cases d
      · exact weighted_02_00_11_00
      · exact weighted_02_00_11_01
      · exact weighted_02_00_11_02
      · exact weighted_02_00_11_03
      · exact weighted_02_00_11_04
      · exact weighted_02_00_11_05
      · exact weighted_02_00_11_06
      · exact weighted_02_00_11_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_11

end Paper7MomentGapNumeric
