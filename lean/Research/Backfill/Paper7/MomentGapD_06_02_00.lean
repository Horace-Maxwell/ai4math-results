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

theorem row_06_02_00_00 : b4RowContribution (![6, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 8] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 8 = 30
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 228
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_00

theorem weighted_06_02_00_00 : b4RawGapContribution ![6, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 6 2 0 0 0 row_06_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_00

theorem row_06_02_00_01 : b4RowContribution (![6, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 9] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 9 = 31
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_01

theorem weighted_06_02_00_01 : b4RawGapContribution ![6, 2, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 0 :=
      b4GapContribution_from_row 6 2 0 1 0 row_06_02_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_01

theorem row_06_02_00_02 : b4RowContribution (![6, 8, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 10] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 10 = 32
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 264 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 264
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_02

theorem weighted_06_02_00_02 : b4RawGapContribution ![6, 2, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 0 :=
      b4GapContribution_from_row 6 2 0 2 0 row_06_02_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_02

theorem row_06_02_00_03 : b4RowContribution (![6, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 11 = 33
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 285
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_03

theorem weighted_06_02_00_03 : b4RawGapContribution ![6, 2, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 0 :=
      b4GapContribution_from_row 6 2 0 3 0 row_06_02_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_03

theorem row_06_02_00_04 : b4RowContribution (![6, 8, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 12 = 34
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_04

theorem weighted_06_02_00_04 : b4RawGapContribution ![6, 2, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 0 :=
      b4GapContribution_from_row 6 2 0 4 0 row_06_02_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_04

theorem row_06_02_00_05 : b4RowContribution (![6, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 13 = 35
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_05

theorem weighted_06_02_00_05 : b4RawGapContribution ![6, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 6 2 0 5 0 row_06_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_05

theorem row_06_02_00_06 : b4RowContribution (![6, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 14 = 36
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_06

theorem weighted_06_02_00_06 : b4RawGapContribution ![6, 2, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 0 :=
      b4GapContribution_from_row 6 2 0 6 0 row_06_02_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_06

theorem row_06_02_00_07 : b4RowContribution (![6, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 8, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 8 + 15 = 37
    decide
  have hzsq : (∑ i, (((![6, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_00_07

theorem weighted_06_02_00_07 : b4RawGapContribution ![6, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 6 2 0 7 0 row_06_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_00_07

def dvalues_06_02_00 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_02_00

theorem dblock_06_02_00 : b4GapPatternDBlock 6 2 0 = 0 := by
  calc
    b4GapPatternDBlock 6 2 0 = ∑ d : Fin 8, dvalues_06_02_00 d := by
      apply b4GapDBlock_of_rows 6 2 0 dvalues_06_02_00
      intro d
      fin_cases d
      · exact weighted_06_02_00_00
      · exact weighted_06_02_00_01
      · exact weighted_06_02_00_02
      · exact weighted_06_02_00_03
      · exact weighted_06_02_00_04
      · exact weighted_06_02_00_05
      · exact weighted_06_02_00_06
      · exact weighted_06_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_02_00

end Paper7MomentGapNumeric
