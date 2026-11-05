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

theorem row_00_01_16_00 : b4RowContribution (![0, 1, 17, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 17, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 17 + 17 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 17, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 17^2 + 17^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_16_00

theorem weighted_00_01_16_00 : b4RawGapContribution ![0, 1, 16, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 16, 0] = b4GapPatternWeight 1 16 0 * 0 :=
      b4GapContribution_from_row 0 1 16 0 0 row_00_01_16_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_16_00

theorem row_00_01_16_01 : b4RowContribution (![0, 1, 17, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 17, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 17 + 18 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 17, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 17^2 + 18^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_16_01

theorem weighted_00_01_16_01 : b4RawGapContribution ![0, 1, 16, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 16, 1] = b4GapPatternWeight 1 16 1 * 0 :=
      b4GapContribution_from_row 0 1 16 1 0 row_00_01_16_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_16_01

theorem row_00_01_16_02 : b4RowContribution (![0, 1, 17, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 17, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 17 + 19 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 17, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 651 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 17^2 + 19^2 = 651
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_16_02

theorem weighted_00_01_16_02 : b4RawGapContribution ![0, 1, 16, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 16, 2] = b4GapPatternWeight 1 16 2 * 0 :=
      b4GapContribution_from_row 0 1 16 2 0 row_00_01_16_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_16_02

def dvalues_00_01_16 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_16

theorem dblock_00_01_16 : b4GapPatternDBlock 0 1 16 = 0 := by
  calc
    b4GapPatternDBlock 0 1 16 = ∑ d : Fin 3, dvalues_00_01_16 d := by
      apply b4GapDBlock_of_rows 0 1 16 dvalues_00_01_16
      intro d
      fin_cases d
      · exact weighted_00_01_16_00
      · exact weighted_00_01_16_01
      · exact weighted_00_01_16_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_16

end Paper7MomentGapNumeric
