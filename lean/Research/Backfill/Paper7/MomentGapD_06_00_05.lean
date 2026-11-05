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

theorem row_06_00_05_00 : b4RowContribution (![6, 6, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 11, 11] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 11 + 11 = 34
    decide
  have hzsq : (∑ i, (((![6, 6, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 11^2 + 11^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_05_00

theorem weighted_06_00_05_00 : b4RawGapContribution ![6, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 6 0 5 0 0 row_06_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_05_00

theorem row_06_00_05_01 : b4RowContribution (![6, 6, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 11, 12] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 11 + 12 = 35
    decide
  have hzsq : (∑ i, (((![6, 6, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 337 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 11^2 + 12^2 = 337
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_05_01

theorem weighted_06_00_05_01 : b4RawGapContribution ![6, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 6 0 5 1 0 row_06_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_05_01

theorem row_06_00_05_02 : b4RowContribution (![6, 6, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 11, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 11 + 13 = 36
    decide
  have hzsq : (∑ i, (((![6, 6, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 11^2 + 13^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_05_02

theorem weighted_06_00_05_02 : b4RawGapContribution ![6, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 6 0 5 2 0 row_06_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_05_02

theorem row_06_00_05_03 : b4RowContribution (![6, 6, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 11, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 11 + 14 = 37
    decide
  have hzsq : (∑ i, (((![6, 6, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 11^2 + 14^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_05_03

theorem weighted_06_00_05_03 : b4RawGapContribution ![6, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 6 0 5 3 0 row_06_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_05_03

def dvalues_06_00_05 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_00_05

theorem dblock_06_00_05 : b4GapPatternDBlock 6 0 5 = 0 := by
  calc
    b4GapPatternDBlock 6 0 5 = ∑ d : Fin 4, dvalues_06_00_05 d := by
      apply b4GapDBlock_of_rows 6 0 5 dvalues_06_00_05
      intro d
      fin_cases d
      · exact weighted_06_00_05_00
      · exact weighted_06_00_05_01
      · exact weighted_06_00_05_02
      · exact weighted_06_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_00_05

end Paper7MomentGapNumeric
