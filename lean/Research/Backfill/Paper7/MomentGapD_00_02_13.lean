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

theorem row_00_02_13_00 : b4RowContribution (![0, 2, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 15^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_00

theorem weighted_00_02_13_00 : b4RawGapContribution ![0, 2, 13, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 0] = b4GapPatternWeight 2 13 0 * 0 :=
      b4GapContribution_from_row 0 2 13 0 0 row_00_02_13_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_00

theorem row_00_02_13_01 : b4RowContribution (![0, 2, 15, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 16^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_01

theorem weighted_00_02_13_01 : b4RawGapContribution ![0, 2, 13, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 1] = b4GapPatternWeight 2 13 1 * 0 :=
      b4GapContribution_from_row 0 2 13 1 0 row_00_02_13_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_01

theorem row_00_02_13_02 : b4RowContribution (![0, 2, 15, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 17^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_02

theorem weighted_00_02_13_02 : b4RawGapContribution ![0, 2, 13, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 2] = b4GapPatternWeight 2 13 2 * 0 :=
      b4GapContribution_from_row 0 2 13 2 0 row_00_02_13_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_02

theorem row_00_02_13_03 : b4RowContribution (![0, 2, 15, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 553 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 18^2 = 553
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_03

theorem weighted_00_02_13_03 : b4RawGapContribution ![0, 2, 13, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 3] = b4GapPatternWeight 2 13 3 * 0 :=
      b4GapContribution_from_row 0 2 13 3 0 row_00_02_13_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_03

theorem row_00_02_13_04 : b4RowContribution (![0, 2, 15, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 590 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 19^2 = 590
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_04

theorem weighted_00_02_13_04 : b4RawGapContribution ![0, 2, 13, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 4] = b4GapPatternWeight 2 13 4 * 0 :=
      b4GapContribution_from_row 0 2 13 4 0 row_00_02_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_04

theorem row_00_02_13_05 : b4RowContribution (![0, 2, 15, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 15, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 15 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 15, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 629 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 15^2 + 20^2 = 629
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_13_05

theorem weighted_00_02_13_05 : b4RawGapContribution ![0, 2, 13, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 13, 5] = b4GapPatternWeight 2 13 5 * 0 :=
      b4GapContribution_from_row 0 2 13 5 0 row_00_02_13_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_13_05

def dvalues_00_02_13 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_13

theorem dblock_00_02_13 : b4GapPatternDBlock 0 2 13 = 0 := by
  calc
    b4GapPatternDBlock 0 2 13 = ∑ d : Fin 6, dvalues_00_02_13 d := by
      apply b4GapDBlock_of_rows 0 2 13 dvalues_00_02_13
      intro d
      fin_cases d
      · exact weighted_00_02_13_00
      · exact weighted_00_02_13_01
      · exact weighted_00_02_13_02
      · exact weighted_00_02_13_03
      · exact weighted_00_02_13_04
      · exact weighted_00_02_13_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_13

end Paper7MomentGapNumeric
