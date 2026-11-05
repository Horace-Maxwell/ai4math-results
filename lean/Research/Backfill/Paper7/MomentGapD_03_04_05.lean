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

theorem row_03_04_05_00 : b4RowContribution (![3, 7, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 12, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 12 + 12 = 34
    decide
  have hzsq : (∑ i, (((![3, 7, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 12^2 + 12^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_05_00

theorem weighted_03_04_05_00 : b4RawGapContribution ![3, 4, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 5, 0] = b4GapPatternWeight 4 5 0 * 0 :=
      b4GapContribution_from_row 3 4 5 0 0 row_03_04_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_05_00

theorem row_03_04_05_01 : b4RowContribution (![3, 7, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 12, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 12 + 13 = 35
    decide
  have hzsq : (∑ i, (((![3, 7, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 12^2 + 13^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_05_01

theorem weighted_03_04_05_01 : b4RawGapContribution ![3, 4, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 5, 1] = b4GapPatternWeight 4 5 1 * 0 :=
      b4GapContribution_from_row 3 4 5 1 0 row_03_04_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_05_01

theorem row_03_04_05_02 : b4RowContribution (![3, 7, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 12, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 12 + 14 = 36
    decide
  have hzsq : (∑ i, (((![3, 7, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 12^2 + 14^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_05_02

theorem weighted_03_04_05_02 : b4RawGapContribution ![3, 4, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 5, 2] = b4GapPatternWeight 4 5 2 * 0 :=
      b4GapContribution_from_row 3 4 5 2 0 row_03_04_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_05_02

theorem row_03_04_05_03 : b4RowContribution (![3, 7, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 12, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 12 + 15 = 37
    decide
  have hzsq : (∑ i, (((![3, 7, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 12^2 + 15^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_05_03

theorem weighted_03_04_05_03 : b4RawGapContribution ![3, 4, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 5, 3] = b4GapPatternWeight 4 5 3 * 0 :=
      b4GapContribution_from_row 3 4 5 3 0 row_03_04_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_05_03

def dvalues_03_04_05 : Fin 4 → ℕ := ![0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_04_05

theorem dblock_03_04_05 : b4GapPatternDBlock 3 4 5 = 0 := by
  calc
    b4GapPatternDBlock 3 4 5 = ∑ d : Fin 4, dvalues_03_04_05 d := by
      apply b4GapDBlock_of_rows 3 4 5 dvalues_03_04_05
      intro d
      fin_cases d
      · exact weighted_03_04_05_00
      · exact weighted_03_04_05_01
      · exact weighted_03_04_05_02
      · exact weighted_03_04_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_04_05

end Paper7MomentGapNumeric
