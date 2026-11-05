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

theorem row_06_04_00_00 : b4RowContribution (![6, 10, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 10, 10, 10] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 10 + 10 + 10 = 36
    decide
  have hzsq : (∑ i, (((![6, 10, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 336 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 10^2 + 10^2 + 10^2 = 336
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_04_00_00

theorem weighted_06_04_00_00 : b4RawGapContribution ![6, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 6 4 0 0 0 row_06_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_04_00_00

theorem row_06_04_00_01 : b4RowContribution (![6, 10, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 10, 10, 11] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 10 + 10 + 11 = 37
    decide
  have hzsq : (∑ i, (((![6, 10, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 10^2 + 10^2 + 11^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_04_00_01

theorem weighted_06_04_00_01 : b4RawGapContribution ![6, 4, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 0 :=
      b4GapContribution_from_row 6 4 0 1 0 row_06_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_04_00_01

def dvalues_06_04_00 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_04_00

theorem dblock_06_04_00 : b4GapPatternDBlock 6 4 0 = 0 := by
  calc
    b4GapPatternDBlock 6 4 0 = ∑ d : Fin 2, dvalues_06_04_00 d := by
      apply b4GapDBlock_of_rows 6 4 0 dvalues_06_04_00
      intro d
      fin_cases d
      · exact weighted_06_04_00_00
      · exact weighted_06_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_04_00

end Paper7MomentGapNumeric
