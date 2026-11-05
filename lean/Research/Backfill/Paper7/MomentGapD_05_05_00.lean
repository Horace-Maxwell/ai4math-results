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

theorem row_05_05_00_00 : b4RowContribution (![5, 10, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 10, 10, 10] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 10 + 10 + 10 = 35
    decide
  have hzsq : (∑ i, (((![5, 10, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 10^2 + 10^2 + 10^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_05_00_00

theorem weighted_05_05_00_00 : b4RawGapContribution ![5, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 5 5 0 0 0 row_05_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_05_00_00

theorem row_05_05_00_01 : b4RowContribution (![5, 10, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 10, 10, 11] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 10 + 10 + 11 = 36
    decide
  have hzsq : (∑ i, (((![5, 10, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 10^2 + 10^2 + 11^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_05_00_01

theorem weighted_05_05_00_01 : b4RawGapContribution ![5, 5, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 0 :=
      b4GapContribution_from_row 5 5 0 1 0 row_05_05_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_05_00_01

theorem row_05_05_00_02 : b4RowContribution (![5, 10, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 10, 10, 12] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 10 + 10 + 12 = 37
    decide
  have hzsq : (∑ i, (((![5, 10, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 10^2 + 10^2 + 12^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_05_00_02

theorem weighted_05_05_00_02 : b4RawGapContribution ![5, 5, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 0 :=
      b4GapContribution_from_row 5 5 0 2 0 row_05_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_05_00_02

def dvalues_05_05_00 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_05_00

theorem dblock_05_05_00 : b4GapPatternDBlock 5 5 0 = 0 := by
  calc
    b4GapPatternDBlock 5 5 0 = ∑ d : Fin 3, dvalues_05_05_00 d := by
      apply b4GapDBlock_of_rows 5 5 0 dvalues_05_05_00
      intro d
      fin_cases d
      · exact weighted_05_05_00_00
      · exact weighted_05_05_00_01
      · exact weighted_05_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_05_00

end Paper7MomentGapNumeric
