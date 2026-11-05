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

theorem row_08_00_02_00 : b4RowContribution (![8, 8, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 10, 10] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 10 + 10 = 36
    decide
  have hzsq : (∑ i, (((![8, 8, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 10^2 + 10^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_02_00

theorem weighted_08_00_02_00 : b4RawGapContribution ![8, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 8 0 2 0 0 row_08_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_02_00

theorem row_08_00_02_01 : b4RowContribution (![8, 8, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![8, 8, 10, 11] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 8 + 8 + 10 + 11 = 37
    decide
  have hzsq : (∑ i, (((![8, 8, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (8 : ℤ)^2 + 8^2 + 10^2 + 11^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_08_00_02_01

theorem weighted_08_00_02_01 : b4RawGapContribution ![8, 0, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![8, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 0 :=
      b4GapContribution_from_row 8 0 2 1 0 row_08_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_08_00_02_01

def dvalues_08_00_02 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_08_00_02

theorem dblock_08_00_02 : b4GapPatternDBlock 8 0 2 = 0 := by
  calc
    b4GapPatternDBlock 8 0 2 = ∑ d : Fin 2, dvalues_08_00_02 d := by
      apply b4GapDBlock_of_rows 8 0 2 dvalues_08_00_02
      intro d
      fin_cases d
      · exact weighted_08_00_02_00
      · exact weighted_08_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_08_00_02

end Paper7MomentGapNumeric
