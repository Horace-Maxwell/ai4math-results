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

theorem row_02_00_12_00 : b4RowContribution (![2, 2, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 14 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 14^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_00

theorem weighted_02_00_12_00 : b4RawGapContribution ![2, 0, 12, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 0] = b4GapPatternWeight 0 12 0 * 0 :=
      b4GapContribution_from_row 2 0 12 0 0 row_02_00_12_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_00

theorem row_02_00_12_01 : b4RowContribution (![2, 2, 14, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 15 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 15^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_01

theorem weighted_02_00_12_01 : b4RawGapContribution ![2, 0, 12, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 1] = b4GapPatternWeight 0 12 1 * 0 :=
      b4GapContribution_from_row 2 0 12 1 0 row_02_00_12_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_01

theorem row_02_00_12_02 : b4RowContribution (![2, 2, 14, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 16 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 16^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_02

theorem weighted_02_00_12_02 : b4RawGapContribution ![2, 0, 12, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 2] = b4GapPatternWeight 0 12 2 * 0 :=
      b4GapContribution_from_row 2 0 12 2 0 row_02_00_12_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_02

theorem row_02_00_12_03 : b4RowContribution (![2, 2, 14, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 17 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 17^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_03

theorem weighted_02_00_12_03 : b4RawGapContribution ![2, 0, 12, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 3] = b4GapPatternWeight 0 12 3 * 0 :=
      b4GapContribution_from_row 2 0 12 3 0 row_02_00_12_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_03

theorem row_02_00_12_04 : b4RowContribution (![2, 2, 14, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 18 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 528 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 18^2 = 528
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_04

theorem weighted_02_00_12_04 : b4RawGapContribution ![2, 0, 12, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 4] = b4GapPatternWeight 0 12 4 * 0 :=
      b4GapContribution_from_row 2 0 12 4 0 row_02_00_12_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_04

theorem row_02_00_12_05 : b4RowContribution (![2, 2, 14, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 14, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 14 + 19 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 565 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 14^2 + 19^2 = 565
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_12_05

theorem weighted_02_00_12_05 : b4RawGapContribution ![2, 0, 12, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 12, 5] = b4GapPatternWeight 0 12 5 * 0 :=
      b4GapContribution_from_row 2 0 12 5 0 row_02_00_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_12_05

def dvalues_02_00_12 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_12

theorem dblock_02_00_12 : b4GapPatternDBlock 2 0 12 = 0 := by
  calc
    b4GapPatternDBlock 2 0 12 = ∑ d : Fin 6, dvalues_02_00_12 d := by
      apply b4GapDBlock_of_rows 2 0 12 dvalues_02_00_12
      intro d
      fin_cases d
      · exact weighted_02_00_12_00
      · exact weighted_02_00_12_01
      · exact weighted_02_00_12_02
      · exact weighted_02_00_12_03
      · exact weighted_02_00_12_04
      · exact weighted_02_00_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_12

end Paper7MomentGapNumeric
