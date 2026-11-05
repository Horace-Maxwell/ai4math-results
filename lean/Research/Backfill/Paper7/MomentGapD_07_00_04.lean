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

theorem row_07_00_04_00 : b4RowContribution (![7, 7, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 11, 11] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 11 + 11 = 36
    decide
  have hzsq : (∑ i, (((![7, 7, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 11^2 + 11^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_04_00

theorem weighted_07_00_04_00 : b4RawGapContribution ![7, 0, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 0 :=
      b4GapContribution_from_row 7 0 4 0 0 row_07_00_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_04_00

theorem row_07_00_04_01 : b4RowContribution (![7, 7, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 11, 12] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 11 + 12 = 37
    decide
  have hzsq : (∑ i, (((![7, 7, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 11^2 + 12^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_04_01

theorem weighted_07_00_04_01 : b4RawGapContribution ![7, 0, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 0 :=
      b4GapContribution_from_row 7 0 4 1 0 row_07_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_04_01

def dvalues_07_00_04 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_00_04

theorem dblock_07_00_04 : b4GapPatternDBlock 7 0 4 = 0 := by
  calc
    b4GapPatternDBlock 7 0 4 = ∑ d : Fin 2, dvalues_07_00_04 d := by
      apply b4GapDBlock_of_rows 7 0 4 dvalues_07_00_04
      intro d
      fin_cases d
      · exact weighted_07_00_04_00
      · exact weighted_07_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_00_04

end Paper7MomentGapNumeric
