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

theorem row_01_11_00_00 : b4RowContribution (![1, 12, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 12, 12, 12] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 12 + 12 + 12 = 37
    decide
  have hzsq : (∑ i, (((![1, 12, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 12^2 + 12^2 + 12^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_11_00_00

theorem weighted_01_11_00_00 : b4RawGapContribution ![1, 11, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 11, 0, 0] = b4GapPatternWeight 11 0 0 * 0 :=
      b4GapContribution_from_row 1 11 0 0 0 row_01_11_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_11_00_00

def dvalues_01_11_00 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_01_11_00

theorem dblock_01_11_00 : b4GapPatternDBlock 1 11 0 = 0 := by
  calc
    b4GapPatternDBlock 1 11 0 = ∑ d : Fin 1, dvalues_01_11_00 d := by
      apply b4GapDBlock_of_rows 1 11 0 dvalues_01_11_00
      intro d
      fin_cases d
      · exact weighted_01_11_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_11_00

end Paper7MomentGapNumeric
