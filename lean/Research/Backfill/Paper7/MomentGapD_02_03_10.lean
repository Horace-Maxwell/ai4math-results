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

theorem row_02_03_10_00 : b4RowContribution (![2, 5, 15, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 15, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 15 + 15 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 15, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 479 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 15^2 + 15^2 = 479
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_10_00

theorem weighted_02_03_10_00 : b4RawGapContribution ![2, 3, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 10, 0] = b4GapPatternWeight 3 10 0 * 0 :=
      b4GapContribution_from_row 2 3 10 0 0 row_02_03_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_10_00

def dvalues_02_03_10 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_10

theorem dblock_02_03_10 : b4GapPatternDBlock 2 3 10 = 0 := by
  calc
    b4GapPatternDBlock 2 3 10 = ∑ d : Fin 1, dvalues_02_03_10 d := by
      apply b4GapDBlock_of_rows 2 3 10 dvalues_02_03_10
      intro d
      fin_cases d
      · exact weighted_02_03_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_10

end Paper7MomentGapNumeric
