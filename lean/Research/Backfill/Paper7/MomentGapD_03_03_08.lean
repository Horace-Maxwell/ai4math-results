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

theorem row_03_03_08_00 : b4RowContribution (![3, 6, 14, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 14, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 14 + 14 = 37
    decide
  have hzsq : (∑ i, (((![3, 6, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 14^2 + 14^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_08_00

theorem weighted_03_03_08_00 : b4RawGapContribution ![3, 3, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 8, 0] = b4GapPatternWeight 3 8 0 * 0 :=
      b4GapContribution_from_row 3 3 8 0 0 row_03_03_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_08_00

def dvalues_03_03_08 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_03_03_08

theorem dblock_03_03_08 : b4GapPatternDBlock 3 3 8 = 0 := by
  calc
    b4GapPatternDBlock 3 3 8 = ∑ d : Fin 1, dvalues_03_03_08 d := by
      apply b4GapDBlock_of_rows 3 3 8 dvalues_03_03_08
      intro d
      fin_cases d
      · exact weighted_03_03_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_03_08

end Paper7MomentGapNumeric
