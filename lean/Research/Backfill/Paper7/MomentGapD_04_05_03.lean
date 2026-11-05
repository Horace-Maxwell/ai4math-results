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

theorem row_04_05_03_00 : b4RowContribution (![4, 9, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 12, 12] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 12 + 12 = 37
    decide
  have hzsq : (∑ i, (((![4, 9, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 12^2 + 12^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_03_00

theorem weighted_04_05_03_00 : b4RawGapContribution ![4, 5, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 3, 0] = b4GapPatternWeight 5 3 0 * 0 :=
      b4GapContribution_from_row 4 5 3 0 0 row_04_05_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_03_00

def dvalues_04_05_03 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.dvalues_04_05_03

theorem dblock_04_05_03 : b4GapPatternDBlock 4 5 3 = 0 := by
  calc
    b4GapPatternDBlock 4 5 3 = ∑ d : Fin 1, dvalues_04_05_03 d := by
      apply b4GapDBlock_of_rows 4 5 3 dvalues_04_05_03
      intro d
      fin_cases d
      · exact weighted_04_05_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_05_03

end Paper7MomentGapNumeric
