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

theorem row_00_05_10_00 : b4RowContribution (![0, 5, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 15, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 15 + 15 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 15^2 + 15^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_10_00

theorem weighted_00_05_10_00 : b4RawGapContribution ![0, 5, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 10, 0] = b4GapPatternWeight 5 10 0 * 0 :=
      b4GapContribution_from_row 0 5 10 0 0 row_00_05_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_10_00

theorem row_00_05_10_01 : b4RowContribution (![0, 5, 15, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 15, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 15 + 16 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 15, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 15^2 + 16^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_10_01

theorem weighted_00_05_10_01 : b4RawGapContribution ![0, 5, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 10, 1] = b4GapPatternWeight 5 10 1 * 0 :=
      b4GapContribution_from_row 0 5 10 1 0 row_00_05_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_10_01

theorem row_00_05_10_02 : b4RowContribution (![0, 5, 15, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 15, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 15 + 17 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 15, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 539 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 15^2 + 17^2 = 539
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_10_02

theorem weighted_00_05_10_02 : b4RawGapContribution ![0, 5, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 10, 2] = b4GapPatternWeight 5 10 2 * 0 :=
      b4GapContribution_from_row 0 5 10 2 0 row_00_05_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_10_02

def dvalues_00_05_10 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_10

theorem dblock_00_05_10 : b4GapPatternDBlock 0 5 10 = 0 := by
  calc
    b4GapPatternDBlock 0 5 10 = ∑ d : Fin 3, dvalues_00_05_10 d := by
      apply b4GapDBlock_of_rows 0 5 10 dvalues_00_05_10
      intro d
      fin_cases d
      · exact weighted_00_05_10_00
      · exact weighted_00_05_10_01
      · exact weighted_00_05_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_10

end Paper7MomentGapNumeric
