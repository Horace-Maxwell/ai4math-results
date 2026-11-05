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

theorem row_00_02_12_00 : b4RowContribution (![0, 2, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 14^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_00

theorem weighted_00_02_12_00 : b4RawGapContribution ![0, 2, 12, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 0] = b4GapPatternWeight 2 12 0 * 0 :=
      b4GapContribution_from_row 0 2 12 0 0 row_00_02_12_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_00

theorem row_00_02_12_01 : b4RowContribution (![0, 2, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 15^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_01

theorem weighted_00_02_12_01 : b4RawGapContribution ![0, 2, 12, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 1] = b4GapPatternWeight 2 12 1 * 0 :=
      b4GapContribution_from_row 0 2 12 1 0 row_00_02_12_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_01

theorem row_00_02_12_02 : b4RowContribution (![0, 2, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 456 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 16^2 = 456
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_02

theorem weighted_00_02_12_02 : b4RawGapContribution ![0, 2, 12, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 2] = b4GapPatternWeight 2 12 2 * 0 :=
      b4GapContribution_from_row 0 2 12 2 0 row_00_02_12_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_02

theorem row_00_02_12_03 : b4RowContribution (![0, 2, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 17^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_03

theorem weighted_00_02_12_03 : b4RawGapContribution ![0, 2, 12, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 3] = b4GapPatternWeight 2 12 3 * 0 :=
      b4GapContribution_from_row 0 2 12 3 0 row_00_02_12_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_03

theorem row_00_02_12_04 : b4RowContribution (![0, 2, 14, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 524 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 18^2 = 524
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_04

theorem weighted_00_02_12_04 : b4RawGapContribution ![0, 2, 12, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 4] = b4GapPatternWeight 2 12 4 * 0 :=
      b4GapContribution_from_row 0 2 12 4 0 row_00_02_12_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_04

theorem row_00_02_12_05 : b4RowContribution (![0, 2, 14, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 561 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 19^2 = 561
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_05

theorem weighted_00_02_12_05 : b4RawGapContribution ![0, 2, 12, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 5] = b4GapPatternWeight 2 12 5 * 0 :=
      b4GapContribution_from_row 0 2 12 5 0 row_00_02_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_05

theorem row_00_02_12_06 : b4RowContribution (![0, 2, 14, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 600 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 20^2 = 600
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_06

theorem weighted_00_02_12_06 : b4RawGapContribution ![0, 2, 12, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 6] = b4GapPatternWeight 2 12 6 * 0 :=
      b4GapContribution_from_row 0 2 12 6 0 row_00_02_12_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_06

theorem row_00_02_12_07 : b4RowContribution (![0, 2, 14, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 14, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 14 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 14, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 641 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 14^2 + 21^2 = 641
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_12_07

theorem weighted_00_02_12_07 : b4RawGapContribution ![0, 2, 12, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 12, 7] = b4GapPatternWeight 2 12 7 * 0 :=
      b4GapContribution_from_row 0 2 12 7 0 row_00_02_12_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_12_07

def dvalues_00_02_12 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_12

theorem dblock_00_02_12 : b4GapPatternDBlock 0 2 12 = 0 := by
  calc
    b4GapPatternDBlock 0 2 12 = ∑ d : Fin 8, dvalues_00_02_12 d := by
      apply b4GapDBlock_of_rows 0 2 12 dvalues_00_02_12
      intro d
      fin_cases d
      · exact weighted_00_02_12_00
      · exact weighted_00_02_12_01
      · exact weighted_00_02_12_02
      · exact weighted_00_02_12_03
      · exact weighted_00_02_12_04
      · exact weighted_00_02_12_05
      · exact weighted_00_02_12_06
      · exact weighted_00_02_12_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_12

end Paper7MomentGapNumeric
