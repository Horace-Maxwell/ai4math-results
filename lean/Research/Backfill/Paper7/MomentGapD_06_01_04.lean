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

theorem row_06_01_04_00 : b4RowContribution (![6, 7, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 11, 11] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 11 + 11 = 35
    decide
  have hzsq : (∑ i, (((![6, 7, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 11^2 + 11^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_04_00

theorem weighted_06_01_04_00 : b4RawGapContribution ![6, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 6 1 4 0 0 row_06_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_04_00

theorem row_06_01_04_01 : b4RowContribution (![6, 7, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 11, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 11 + 12 = 36
    decide
  have hzsq : (∑ i, (((![6, 7, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 11^2 + 12^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_04_01

theorem weighted_06_01_04_01 : b4RawGapContribution ![6, 1, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 0 :=
      b4GapContribution_from_row 6 1 4 1 0 row_06_01_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_04_01

theorem row_06_01_04_02 : b4RowContribution (![6, 7, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 11, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 11 + 13 = 37
    decide
  have hzsq : (∑ i, (((![6, 7, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 11^2 + 13^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_04_02

theorem weighted_06_01_04_02 : b4RawGapContribution ![6, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 6 1 4 2 0 row_06_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_04_02

def dvalues_06_01_04 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_01_04

theorem dblock_06_01_04 : b4GapPatternDBlock 6 1 4 = 0 := by
  calc
    b4GapPatternDBlock 6 1 4 = ∑ d : Fin 3, dvalues_06_01_04 d := by
      apply b4GapDBlock_of_rows 6 1 4 dvalues_06_01_04
      intro d
      fin_cases d
      · exact weighted_06_01_04_00
      · exact weighted_06_01_04_01
      · exact weighted_06_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_01_04

end Paper7MomentGapNumeric
