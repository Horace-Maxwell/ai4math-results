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

theorem row_01_04_10_00 : b4RowContribution (![1, 5, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 15, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 15 + 15 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 476 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 15^2 + 15^2 = 476
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_10_00

theorem weighted_01_04_10_00 : b4RawGapContribution ![1, 4, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 10, 0] = b4GapPatternWeight 4 10 0 * 0 :=
      b4GapContribution_from_row 1 4 10 0 0 row_01_04_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_10_00

theorem row_01_04_10_01 : b4RowContribution (![1, 5, 15, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 15, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 15 + 16 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 15, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 15^2 + 16^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_10_01

theorem weighted_01_04_10_01 : b4RawGapContribution ![1, 4, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 10, 1] = b4GapPatternWeight 4 10 1 * 0 :=
      b4GapContribution_from_row 1 4 10 1 0 row_01_04_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_10_01

def dvalues_01_04_10 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_10

theorem dblock_01_04_10 : b4GapPatternDBlock 1 4 10 = 0 := by
  calc
    b4GapPatternDBlock 1 4 10 = ∑ d : Fin 2, dvalues_01_04_10 d := by
      apply b4GapDBlock_of_rows 1 4 10 dvalues_01_04_10
      intro d
      fin_cases d
      · exact weighted_01_04_10_00
      · exact weighted_01_04_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_10

end Paper7MomentGapNumeric
