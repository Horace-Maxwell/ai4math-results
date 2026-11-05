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

theorem row_00_02_11_00 : b4RowContribution (![0, 2, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 13 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 13^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_00

theorem weighted_00_02_11_00 : b4RawGapContribution ![0, 2, 11, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 0] = b4GapPatternWeight 2 11 0 * 0 :=
      b4GapContribution_from_row 0 2 11 0 0 row_00_02_11_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_00

theorem row_00_02_11_01 : b4RowContribution (![0, 2, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 14^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_01

theorem weighted_00_02_11_01 : b4RawGapContribution ![0, 2, 11, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 1] = b4GapPatternWeight 2 11 1 * 0 :=
      b4GapContribution_from_row 0 2 11 1 0 row_00_02_11_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_01

theorem row_00_02_11_02 : b4RowContribution (![0, 2, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 15^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_02

theorem weighted_00_02_11_02 : b4RawGapContribution ![0, 2, 11, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 2] = b4GapPatternWeight 2 11 2 * 0 :=
      b4GapContribution_from_row 0 2 11 2 0 row_00_02_11_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_02

theorem row_00_02_11_03 : b4RowContribution (![0, 2, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 16^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_03

theorem weighted_00_02_11_03 : b4RawGapContribution ![0, 2, 11, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 3] = b4GapPatternWeight 2 11 3 * 0 :=
      b4GapContribution_from_row 0 2 11 3 0 row_00_02_11_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_03

theorem row_00_02_11_04 : b4RowContribution (![0, 2, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 17^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_04

theorem weighted_00_02_11_04 : b4RawGapContribution ![0, 2, 11, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 4] = b4GapPatternWeight 2 11 4 * 0 :=
      b4GapContribution_from_row 0 2 11 4 0 row_00_02_11_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_04

theorem row_00_02_11_05 : b4RowContribution (![0, 2, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 497 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 18^2 = 497
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_05

theorem weighted_00_02_11_05 : b4RawGapContribution ![0, 2, 11, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 5] = b4GapPatternWeight 2 11 5 * 0 :=
      b4GapContribution_from_row 0 2 11 5 0 row_00_02_11_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_05

theorem row_00_02_11_06 : b4RowContribution (![0, 2, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 19^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_06

theorem weighted_00_02_11_06 : b4RawGapContribution ![0, 2, 11, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 6] = b4GapPatternWeight 2 11 6 * 0 :=
      b4GapContribution_from_row 0 2 11 6 0 row_00_02_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_06

theorem row_00_02_11_07 : b4RowContribution (![0, 2, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 20^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_07

theorem weighted_00_02_11_07 : b4RawGapContribution ![0, 2, 11, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 7] = b4GapPatternWeight 2 11 7 * 0 :=
      b4GapContribution_from_row 0 2 11 7 0 row_00_02_11_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_07

theorem row_00_02_11_08 : b4RowContribution (![0, 2, 13, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 21^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_08

theorem weighted_00_02_11_08 : b4RawGapContribution ![0, 2, 11, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 8] = b4GapPatternWeight 2 11 8 * 0 :=
      b4GapContribution_from_row 0 2 11 8 0 row_00_02_11_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_08

theorem row_00_02_11_09 : b4RowContribution (![0, 2, 13, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 13, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 13 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 13, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 657 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 13^2 + 22^2 = 657
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_11_09

theorem weighted_00_02_11_09 : b4RawGapContribution ![0, 2, 11, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 11, 9] = b4GapPatternWeight 2 11 9 * 0 :=
      b4GapContribution_from_row 0 2 11 9 0 row_00_02_11_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_11_09

def dvalues_00_02_11 : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_11

theorem dblock_00_02_11 : b4GapPatternDBlock 0 2 11 = 0 := by
  calc
    b4GapPatternDBlock 0 2 11 = ∑ d : Fin 10, dvalues_00_02_11 d := by
      apply b4GapDBlock_of_rows 0 2 11 dvalues_00_02_11
      intro d
      fin_cases d
      · exact weighted_00_02_11_00
      · exact weighted_00_02_11_01
      · exact weighted_00_02_11_02
      · exact weighted_00_02_11_03
      · exact weighted_00_02_11_04
      · exact weighted_00_02_11_05
      · exact weighted_00_02_11_06
      · exact weighted_00_02_11_07
      · exact weighted_00_02_11_08
      · exact weighted_00_02_11_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_11

end Paper7MomentGapNumeric
