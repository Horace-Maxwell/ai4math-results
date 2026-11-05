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

theorem row_06_01_01_00 : b4RowContribution (![6, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 8] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 8 = 29
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 213
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_00

theorem weighted_06_01_01_00 : b4RawGapContribution ![6, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 6 1 1 0 0 row_06_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_00

theorem row_06_01_01_01 : b4RowContribution (![6, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 9] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 9 = 30
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 230
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_01

theorem weighted_06_01_01_01 : b4RawGapContribution ![6, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 6 1 1 1 0 row_06_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_01

theorem row_06_01_01_02 : b4RowContribution (![6, 7, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 10 = 31
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_02

theorem weighted_06_01_01_02 : b4RawGapContribution ![6, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 6 1 1 2 0 row_06_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_02

theorem row_06_01_01_03 : b4RowContribution (![6, 7, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 11 = 32
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_03

theorem weighted_06_01_01_03 : b4RawGapContribution ![6, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 6 1 1 3 0 row_06_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_03

theorem row_06_01_01_04 : b4RowContribution (![6, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 12 = 33
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_04

theorem weighted_06_01_01_04 : b4RawGapContribution ![6, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 6 1 1 4 0 row_06_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_04

theorem row_06_01_01_05 : b4RowContribution (![6, 7, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 13 = 34
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_05

theorem weighted_06_01_01_05 : b4RawGapContribution ![6, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 6 1 1 5 0 row_06_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_05

theorem row_06_01_01_06 : b4RowContribution (![6, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 14 = 35
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_06

theorem weighted_06_01_01_06 : b4RawGapContribution ![6, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 6 1 1 6 0 row_06_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_06

theorem row_06_01_01_07 : b4RowContribution (![6, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 15 = 36
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_07

theorem weighted_06_01_01_07 : b4RawGapContribution ![6, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 6 1 1 7 0 row_06_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_07

theorem row_06_01_01_08 : b4RowContribution (![6, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 8, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 8 + 16 = 37
    decide
  have hzsq : (∑ i, (((![6, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_01_08

theorem weighted_06_01_01_08 : b4RawGapContribution ![6, 1, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 0 :=
      b4GapContribution_from_row 6 1 1 8 0 row_06_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_01_08

def dvalues_06_01_01 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_01_01

theorem dblock_06_01_01 : b4GapPatternDBlock 6 1 1 = 0 := by
  calc
    b4GapPatternDBlock 6 1 1 = ∑ d : Fin 9, dvalues_06_01_01 d := by
      apply b4GapDBlock_of_rows 6 1 1 dvalues_06_01_01
      intro d
      fin_cases d
      · exact weighted_06_01_01_00
      · exact weighted_06_01_01_01
      · exact weighted_06_01_01_02
      · exact weighted_06_01_01_03
      · exact weighted_06_01_01_04
      · exact weighted_06_01_01_05
      · exact weighted_06_01_01_06
      · exact weighted_06_01_01_07
      · exact weighted_06_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_01_01

end Paper7MomentGapNumeric
