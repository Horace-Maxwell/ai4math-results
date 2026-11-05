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

theorem row_00_03_10_00 : b4RowContribution (![0, 3, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 13 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 13^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_00

theorem weighted_00_03_10_00 : b4RawGapContribution ![0, 3, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 0] = b4GapPatternWeight 3 10 0 * 0 :=
      b4GapContribution_from_row 0 3 10 0 0 row_00_03_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_00

theorem row_00_03_10_01 : b4RowContribution (![0, 3, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 14^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_01

theorem weighted_00_03_10_01 : b4RawGapContribution ![0, 3, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 1] = b4GapPatternWeight 3 10 1 * 0 :=
      b4GapContribution_from_row 0 3 10 1 0 row_00_03_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_01

theorem row_00_03_10_02 : b4RowContribution (![0, 3, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 15^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_02

theorem weighted_00_03_10_02 : b4RawGapContribution ![0, 3, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 2] = b4GapPatternWeight 3 10 2 * 0 :=
      b4GapContribution_from_row 0 3 10 2 0 row_00_03_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_02

theorem row_00_03_10_03 : b4RowContribution (![0, 3, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 16^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_03

theorem weighted_00_03_10_03 : b4RawGapContribution ![0, 3, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 3] = b4GapPatternWeight 3 10 3 * 0 :=
      b4GapContribution_from_row 0 3 10 3 0 row_00_03_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_03

theorem row_00_03_10_04 : b4RowContribution (![0, 3, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 467 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 17^2 = 467
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_04

theorem weighted_00_03_10_04 : b4RawGapContribution ![0, 3, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 4] = b4GapPatternWeight 3 10 4 * 0 :=
      b4GapContribution_from_row 0 3 10 4 0 row_00_03_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_04

theorem row_00_03_10_05 : b4RowContribution (![0, 3, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 18^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_05

theorem weighted_00_03_10_05 : b4RawGapContribution ![0, 3, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 5] = b4GapPatternWeight 3 10 5 * 0 :=
      b4GapContribution_from_row 0 3 10 5 0 row_00_03_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_05

theorem row_00_03_10_06 : b4RowContribution (![0, 3, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 539 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 19^2 = 539
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_06

theorem weighted_00_03_10_06 : b4RawGapContribution ![0, 3, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 6] = b4GapPatternWeight 3 10 6 * 0 :=
      b4GapContribution_from_row 0 3 10 6 0 row_00_03_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_06

theorem row_00_03_10_07 : b4RowContribution (![0, 3, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 20^2 = 578
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_07

theorem weighted_00_03_10_07 : b4RawGapContribution ![0, 3, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 7] = b4GapPatternWeight 3 10 7 * 0 :=
      b4GapContribution_from_row 0 3 10 7 0 row_00_03_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_07

theorem row_00_03_10_08 : b4RowContribution (![0, 3, 13, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 13, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 13 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 13, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 619 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 13^2 + 21^2 = 619
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_10_08

theorem weighted_00_03_10_08 : b4RawGapContribution ![0, 3, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 10, 8] = b4GapPatternWeight 3 10 8 * 0 :=
      b4GapContribution_from_row 0 3 10 8 0 row_00_03_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_10_08

def dvalues_00_03_10 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_10

theorem dblock_00_03_10 : b4GapPatternDBlock 0 3 10 = 0 := by
  calc
    b4GapPatternDBlock 0 3 10 = ∑ d : Fin 9, dvalues_00_03_10 d := by
      apply b4GapDBlock_of_rows 0 3 10 dvalues_00_03_10
      intro d
      fin_cases d
      · exact weighted_00_03_10_00
      · exact weighted_00_03_10_01
      · exact weighted_00_03_10_02
      · exact weighted_00_03_10_03
      · exact weighted_00_03_10_04
      · exact weighted_00_03_10_05
      · exact weighted_00_03_10_06
      · exact weighted_00_03_10_07
      · exact weighted_00_03_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_10

end Paper7MomentGapNumeric
