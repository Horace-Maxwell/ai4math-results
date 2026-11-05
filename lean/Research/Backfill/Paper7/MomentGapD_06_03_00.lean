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

def layers_06_03_00_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 54, 57, 58, 57, 54, 49, 42, 35, 28], ![1, 4, 10, 20, 35, 56, 84, 119, 161, 210, 263, 317, 369, 416, 455, 483, 497, 497, 483]]
#print axioms Paper7MomentGapNumeric.layers_06_03_00_00

theorem cells_06_03_00_00 : QTableValid (![6, 9, 9, 9] : Fin 4 → ℕ) layers_06_03_00_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_03_00_00

theorem valid_06_03_00_00 :
    SparseRowValid (![6, 9, 9, 9] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_06_03_00_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 9, 9, 9] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 6 + 9 + 9 + 9 = 33
      decide
    have hzsq : (∑ i, (((![6, 9, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 9^2 + 9^2 + 9^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_03_00_00
#print axioms Paper7MomentGapNumeric.valid_06_03_00_00

def qvalues_06_03_00_00 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_03_00_00

theorem row_06_03_00_00 : b4RowContribution (![6, 9, 9, 9] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![6, 9, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_06_03_00_00) :=
      sparseRow_sound (![6, 9, 9, 9] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_06_03_00_00) valid_06_03_00_00
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_03_00_00 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_06_03_00_00

theorem weighted_06_03_00_00 : b4RawGapContribution ![6, 3, 0, 0] = 80 := by
  calc
    b4RawGapContribution ![6, 3, 0, 0] = b4GapPatternWeight 3 0 0 * 20 :=
      b4GapContribution_from_row 6 3 0 0 20 row_06_03_00_00
    _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_03_00_00

theorem row_06_03_00_01 : b4RowContribution (![6, 9, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 9, 9, 10] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 9 + 9 + 10 = 34
    decide
  have hzsq : (∑ i, (((![6, 9, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 9^2 + 9^2 + 10^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_03_00_01

theorem weighted_06_03_00_01 : b4RawGapContribution ![6, 3, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 3, 0, 1] = b4GapPatternWeight 3 0 1 * 0 :=
      b4GapContribution_from_row 6 3 0 1 0 row_06_03_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_03_00_01

theorem row_06_03_00_02 : b4RowContribution (![6, 9, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 9, 9, 11] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 9 + 9 + 11 = 35
    decide
  have hzsq : (∑ i, (((![6, 9, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 9^2 + 9^2 + 11^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_03_00_02

theorem weighted_06_03_00_02 : b4RawGapContribution ![6, 3, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 3, 0, 2] = b4GapPatternWeight 3 0 2 * 0 :=
      b4GapContribution_from_row 6 3 0 2 0 row_06_03_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_03_00_02

theorem row_06_03_00_03 : b4RowContribution (![6, 9, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 9, 9, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 9 + 9 + 12 = 36
    decide
  have hzsq : (∑ i, (((![6, 9, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 9^2 + 9^2 + 12^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_03_00_03

theorem weighted_06_03_00_03 : b4RawGapContribution ![6, 3, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 3, 0, 3] = b4GapPatternWeight 3 0 3 * 0 :=
      b4GapContribution_from_row 6 3 0 3 0 row_06_03_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_03_00_03

theorem row_06_03_00_04 : b4RowContribution (![6, 9, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 9, 9, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 9 + 9 + 13 = 37
    decide
  have hzsq : (∑ i, (((![6, 9, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 9^2 + 9^2 + 13^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_03_00_04

theorem weighted_06_03_00_04 : b4RawGapContribution ![6, 3, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 3, 0, 4] = b4GapPatternWeight 3 0 4 * 0 :=
      b4GapContribution_from_row 6 3 0 4 0 row_06_03_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_03_00_04

def dvalues_06_03_00 : Fin 5 → ℕ := ![80, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_03_00

theorem dblock_06_03_00 : b4GapPatternDBlock 6 3 0 = 80 := by
  calc
    b4GapPatternDBlock 6 3 0 = ∑ d : Fin 5, dvalues_06_03_00 d := by
      apply b4GapDBlock_of_rows 6 3 0 dvalues_06_03_00
      intro d
      fin_cases d
      · exact weighted_06_03_00_00
      · exact weighted_06_03_00_01
      · exact weighted_06_03_00_02
      · exact weighted_06_03_00_03
      · exact weighted_06_03_00_04
    _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_03_00

end Paper7MomentGapNumeric
