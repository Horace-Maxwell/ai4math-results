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

theorem row_00_02_10_00 : b4RowContribution (![0, 2, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 12 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 12^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_00

theorem weighted_00_02_10_00 : b4RawGapContribution ![0, 2, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 0] = b4GapPatternWeight 2 10 0 * 0 :=
      b4GapContribution_from_row 0 2 10 0 0 row_00_02_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_00

theorem row_00_02_10_01 : b4RowContribution (![0, 2, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 13 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 317 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 13^2 = 317
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_01

theorem weighted_00_02_10_01 : b4RawGapContribution ![0, 2, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 1] = b4GapPatternWeight 2 10 1 * 0 :=
      b4GapContribution_from_row 0 2 10 1 0 row_00_02_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_01

theorem row_00_02_10_02 : b4RowContribution (![0, 2, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 344 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 14^2 = 344
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_02

theorem weighted_00_02_10_02 : b4RawGapContribution ![0, 2, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 2] = b4GapPatternWeight 2 10 2 * 0 :=
      b4GapContribution_from_row 0 2 10 2 0 row_00_02_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_02

theorem row_00_02_10_03 : b4RowContribution (![0, 2, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 15^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_03

theorem weighted_00_02_10_03 : b4RawGapContribution ![0, 2, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 3] = b4GapPatternWeight 2 10 3 * 0 :=
      b4GapContribution_from_row 0 2 10 3 0 row_00_02_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_03

theorem row_00_02_10_04 : b4RowContribution (![0, 2, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 16^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_04

theorem weighted_00_02_10_04 : b4RawGapContribution ![0, 2, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 4] = b4GapPatternWeight 2 10 4 * 0 :=
      b4GapContribution_from_row 0 2 10 4 0 row_00_02_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_04

theorem row_00_02_10_05 : b4RowContribution (![0, 2, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 17^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_05

theorem weighted_00_02_10_05 : b4RawGapContribution ![0, 2, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 5] = b4GapPatternWeight 2 10 5 * 0 :=
      b4GapContribution_from_row 0 2 10 5 0 row_00_02_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_05

theorem row_00_02_10_06 : b4RowContribution (![0, 2, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 472 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 18^2 = 472
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_06

theorem weighted_00_02_10_06 : b4RawGapContribution ![0, 2, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 6] = b4GapPatternWeight 2 10 6 * 0 :=
      b4GapContribution_from_row 0 2 10 6 0 row_00_02_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_06

theorem row_00_02_10_07 : b4RowContribution (![0, 2, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 509 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 19^2 = 509
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_07

theorem weighted_00_02_10_07 : b4RawGapContribution ![0, 2, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 7] = b4GapPatternWeight 2 10 7 * 0 :=
      b4GapContribution_from_row 0 2 10 7 0 row_00_02_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_07

theorem row_00_02_10_08 : b4RowContribution (![0, 2, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 548 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 20^2 = 548
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_08

theorem weighted_00_02_10_08 : b4RawGapContribution ![0, 2, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 8] = b4GapPatternWeight 2 10 8 * 0 :=
      b4GapContribution_from_row 0 2 10 8 0 row_00_02_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_08

theorem row_00_02_10_09 : b4RowContribution (![0, 2, 12, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 589 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 21^2 = 589
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_09

theorem weighted_00_02_10_09 : b4RawGapContribution ![0, 2, 10, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 9] = b4GapPatternWeight 2 10 9 * 0 :=
      b4GapContribution_from_row 0 2 10 9 0 row_00_02_10_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_09

theorem row_00_02_10_10 : b4RowContribution (![0, 2, 12, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 632 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 22^2 = 632
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_10

theorem weighted_00_02_10_10 : b4RawGapContribution ![0, 2, 10, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 10] = b4GapPatternWeight 2 10 10 * 0 :=
      b4GapContribution_from_row 0 2 10 10 0 row_00_02_10_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_10

theorem row_00_02_10_11 : b4RowContribution (![0, 2, 12, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 12, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 12 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 12, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 677 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 12^2 + 23^2 = 677
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_10_11

theorem weighted_00_02_10_11 : b4RawGapContribution ![0, 2, 10, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 10, 11] = b4GapPatternWeight 2 10 11 * 0 :=
      b4GapContribution_from_row 0 2 10 11 0 row_00_02_10_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_10_11

def dvalues_00_02_10 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_10

theorem dblock_00_02_10 : b4GapPatternDBlock 0 2 10 = 0 := by
  calc
    b4GapPatternDBlock 0 2 10 = ∑ d : Fin 12, dvalues_00_02_10 d := by
      apply b4GapDBlock_of_rows 0 2 10 dvalues_00_02_10
      intro d
      fin_cases d
      · exact weighted_00_02_10_00
      · exact weighted_00_02_10_01
      · exact weighted_00_02_10_02
      · exact weighted_00_02_10_03
      · exact weighted_00_02_10_04
      · exact weighted_00_02_10_05
      · exact weighted_00_02_10_06
      · exact weighted_00_02_10_07
      · exact weighted_00_02_10_08
      · exact weighted_00_02_10_09
      · exact weighted_00_02_10_10
      · exact weighted_00_02_10_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_10

end Paper7MomentGapNumeric
