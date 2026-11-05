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

theorem row_00_09_05_00 : b4RowContribution (![0, 9, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 14, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 14 + 14 = 37
    decide
  have hzsq : (∑ i, (((![0, 9, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 14^2 + 14^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_05_00

theorem weighted_00_09_05_00 : b4RawGapContribution ![0, 9, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 5, 0] = b4GapPatternWeight 9 5 0 * 0 :=
      b4GapContribution_from_row 0 9 5 0 0 row_00_09_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_05_00

def dvalues_00_09_05 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_00_09_05

theorem dblock_00_09_05 : b4GapPatternDBlock 0 9 5 = 0 := by
  calc
    b4GapPatternDBlock 0 9 5 = ∑ d : Fin 1, dvalues_00_09_05 d := by
      apply b4GapDBlock_of_rows 0 9 5 dvalues_00_09_05
      intro d
      fin_cases d
      · exact weighted_00_09_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_09_05

end Paper7MomentGapNumeric
