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

theorem row_00_02_15_00 : b4RowContribution (![0, 2, 17, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 17, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 17 + 17 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 17, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 582 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 17^2 + 17^2 = 582
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_15_00

theorem weighted_00_02_15_00 : b4RawGapContribution ![0, 2, 15, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 15, 0] = b4GapPatternWeight 2 15 0 * 0 :=
      b4GapContribution_from_row 0 2 15 0 0 row_00_02_15_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_15_00

theorem row_00_02_15_01 : b4RowContribution (![0, 2, 17, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 17, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 17 + 18 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 17, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 617 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 17^2 + 18^2 = 617
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_15_01

theorem weighted_00_02_15_01 : b4RawGapContribution ![0, 2, 15, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 15, 1] = b4GapPatternWeight 2 15 1 * 0 :=
      b4GapContribution_from_row 0 2 15 1 0 row_00_02_15_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_15_01

def dvalues_00_02_15 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_15

theorem dblock_00_02_15 : b4GapPatternDBlock 0 2 15 = 0 := by
  calc
    b4GapPatternDBlock 0 2 15 = ∑ d : Fin 2, dvalues_00_02_15 d := by
      apply b4GapDBlock_of_rows 0 2 15 dvalues_00_02_15
      intro d
      fin_cases d
      · exact weighted_00_02_15_00
      · exact weighted_00_02_15_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_15

end Paper7MomentGapNumeric
