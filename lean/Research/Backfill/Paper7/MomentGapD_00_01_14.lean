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

theorem row_00_01_14_00 : b4RowContribution (![0, 1, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 15^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_00

theorem weighted_00_01_14_00 : b4RawGapContribution ![0, 1, 14, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 0] = b4GapPatternWeight 1 14 0 * 0 :=
      b4GapContribution_from_row 0 1 14 0 0 row_00_01_14_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_00

theorem row_00_01_14_01 : b4RowContribution (![0, 1, 15, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 16^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_01

theorem weighted_00_01_14_01 : b4RawGapContribution ![0, 1, 14, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 1] = b4GapPatternWeight 1 14 1 * 0 :=
      b4GapContribution_from_row 0 1 14 1 0 row_00_01_14_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_01

theorem row_00_01_14_02 : b4RowContribution (![0, 1, 15, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 515 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 17^2 = 515
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_02

theorem weighted_00_01_14_02 : b4RawGapContribution ![0, 1, 14, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 2] = b4GapPatternWeight 1 14 2 * 0 :=
      b4GapContribution_from_row 0 1 14 2 0 row_00_01_14_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_02

theorem row_00_01_14_03 : b4RowContribution (![0, 1, 15, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 18^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_03

theorem weighted_00_01_14_03 : b4RawGapContribution ![0, 1, 14, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 3] = b4GapPatternWeight 1 14 3 * 0 :=
      b4GapContribution_from_row 0 1 14 3 0 row_00_01_14_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_03

theorem row_00_01_14_04 : b4RowContribution (![0, 1, 15, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 19^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_04

theorem weighted_00_01_14_04 : b4RawGapContribution ![0, 1, 14, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 4] = b4GapPatternWeight 1 14 4 * 0 :=
      b4GapContribution_from_row 0 1 14 4 0 row_00_01_14_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_04

theorem row_00_01_14_05 : b4RowContribution (![0, 1, 15, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 20^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_05

theorem weighted_00_01_14_05 : b4RawGapContribution ![0, 1, 14, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 5] = b4GapPatternWeight 1 14 5 * 0 :=
      b4GapContribution_from_row 0 1 14 5 0 row_00_01_14_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_05

theorem row_00_01_14_06 : b4RowContribution (![0, 1, 15, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 15, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 15 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 15, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 667 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 15^2 + 21^2 = 667
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_14_06

theorem weighted_00_01_14_06 : b4RawGapContribution ![0, 1, 14, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 14, 6] = b4GapPatternWeight 1 14 6 * 0 :=
      b4GapContribution_from_row 0 1 14 6 0 row_00_01_14_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_14_06

def dvalues_00_01_14 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_14

theorem dblock_00_01_14 : b4GapPatternDBlock 0 1 14 = 0 := by
  calc
    b4GapPatternDBlock 0 1 14 = ∑ d : Fin 7, dvalues_00_01_14 d := by
      apply b4GapDBlock_of_rows 0 1 14 dvalues_00_01_14
      intro d
      fin_cases d
      · exact weighted_00_01_14_00
      · exact weighted_00_01_14_01
      · exact weighted_00_01_14_02
      · exact weighted_00_01_14_03
      · exact weighted_00_01_14_04
      · exact weighted_00_01_14_05
      · exact weighted_00_01_14_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_14

end Paper7MomentGapNumeric
