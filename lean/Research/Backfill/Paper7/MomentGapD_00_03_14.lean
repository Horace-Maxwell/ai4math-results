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

theorem row_00_03_14_00 : b4RowContribution (![0, 3, 17, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 17, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 17 + 17 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 17, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 17^2 + 17^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_14_00

theorem weighted_00_03_14_00 : b4RawGapContribution ![0, 3, 14, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 14, 0] = b4GapPatternWeight 3 14 0 * 0 :=
      b4GapContribution_from_row 0 3 14 0 0 row_00_03_14_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_14_00

def dvalues_00_03_14 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_14

theorem dblock_00_03_14 : b4GapPatternDBlock 0 3 14 = 0 := by
  calc
    b4GapPatternDBlock 0 3 14 = ∑ d : Fin 1, dvalues_00_03_14 d := by
      apply b4GapDBlock_of_rows 0 3 14 dvalues_00_03_14
      intro d
      fin_cases d
      · exact weighted_00_03_14_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_14

end Paper7MomentGapNumeric
