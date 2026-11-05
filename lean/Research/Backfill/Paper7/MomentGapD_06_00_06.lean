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

theorem row_06_00_06_00 : b4RowContribution (![6, 6, 12, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 12, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 12 + 12 = 36
    decide
  have hzsq : (∑ i, (((![6, 6, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 12^2 + 12^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_06_00

theorem weighted_06_00_06_00 : b4RawGapContribution ![6, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 6 0 6 0 0 row_06_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_06_00

theorem row_06_00_06_01 : b4RowContribution (![6, 6, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 12, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 12 + 13 = 37
    decide
  have hzsq : (∑ i, (((![6, 6, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 12^2 + 13^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_06_01

theorem weighted_06_00_06_01 : b4RawGapContribution ![6, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 6 0 6 1 0 row_06_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_06_01

def dvalues_06_00_06 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_00_06

theorem dblock_06_00_06 : b4GapPatternDBlock 6 0 6 = 0 := by
  calc
    b4GapPatternDBlock 6 0 6 = ∑ d : Fin 2, dvalues_06_00_06 d := by
      apply b4GapDBlock_of_rows 6 0 6 dvalues_06_00_06
      intro d
      fin_cases d
      · exact weighted_06_00_06_00
      · exact weighted_06_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_00_06

end Paper7MomentGapNumeric
