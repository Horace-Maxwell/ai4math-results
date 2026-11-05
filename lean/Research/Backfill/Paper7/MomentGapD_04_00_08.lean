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

theorem row_04_00_08_00 : b4RowContribution (![4, 4, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 12 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 320 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 12^2 = 320
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_00

theorem weighted_04_00_08_00 : b4RawGapContribution ![4, 0, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 0 :=
      b4GapContribution_from_row 4 0 8 0 0 row_04_00_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_00

theorem row_04_00_08_01 : b4RowContribution (![4, 4, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 13 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 13^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_01

theorem weighted_04_00_08_01 : b4RawGapContribution ![4, 0, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 0 :=
      b4GapContribution_from_row 4 0 8 1 0 row_04_00_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_01

theorem row_04_00_08_02 : b4RowContribution (![4, 4, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 14 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 14^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_02

theorem weighted_04_00_08_02 : b4RawGapContribution ![4, 0, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 2] = b4GapPatternWeight 0 8 2 * 0 :=
      b4GapContribution_from_row 4 0 8 2 0 row_04_00_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_02

theorem row_04_00_08_03 : b4RowContribution (![4, 4, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 15 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 15^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_03

theorem weighted_04_00_08_03 : b4RawGapContribution ![4, 0, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 3] = b4GapPatternWeight 0 8 3 * 0 :=
      b4GapContribution_from_row 4 0 8 3 0 row_04_00_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_03

theorem row_04_00_08_04 : b4RowContribution (![4, 4, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 16 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 432 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 16^2 = 432
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_04

theorem weighted_04_00_08_04 : b4RawGapContribution ![4, 0, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 4] = b4GapPatternWeight 0 8 4 * 0 :=
      b4GapContribution_from_row 4 0 8 4 0 row_04_00_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_04

theorem row_04_00_08_05 : b4RowContribution (![4, 4, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 12, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 12 + 17 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 12^2 + 17^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_08_05

theorem weighted_04_00_08_05 : b4RawGapContribution ![4, 0, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 8, 5] = b4GapPatternWeight 0 8 5 * 0 :=
      b4GapContribution_from_row 4 0 8 5 0 row_04_00_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_08_05

def dvalues_04_00_08 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_08

theorem dblock_04_00_08 : b4GapPatternDBlock 4 0 8 = 0 := by
  calc
    b4GapPatternDBlock 4 0 8 = ∑ d : Fin 6, dvalues_04_00_08 d := by
      apply b4GapDBlock_of_rows 4 0 8 dvalues_04_00_08
      intro d
      fin_cases d
      · exact weighted_04_00_08_00
      · exact weighted_04_00_08_01
      · exact weighted_04_00_08_02
      · exact weighted_04_00_08_03
      · exact weighted_04_00_08_04
      · exact weighted_04_00_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_08

end Paper7MomentGapNumeric
