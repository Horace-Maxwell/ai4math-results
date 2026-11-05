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

theorem row_07_00_02_00 : b4RowContribution (![7, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 9, 9] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 9 + 9 = 32
    decide
  have hzsq : (∑ i, (((![7, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_02_00

theorem weighted_07_00_02_00 : b4RawGapContribution ![7, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 7 0 2 0 0 row_07_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_00

def layers_07_00_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 43, 49, 53, 55, 55, 53, 49, 43, 36, 28, 21], ![1, 4, 10, 20, 35, 56, 84, 120, 163, 212, 265, 319, 371, 418, 457, 485, 500, 500, 485]]
#print axioms Paper7MomentGapNumeric.layers_07_00_02_01

theorem cells_07_00_02_01 : QTableValid (![7, 7, 9, 10] : Fin 4 → ℕ) layers_07_00_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_07_00_02_01

theorem valid_07_00_02_01 :
    SparseRowValid (![7, 7, 9, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_07_00_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![7, 7, 9, 10] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 7 + 7 + 9 + 10 = 33
      decide
    have hzsq : (∑ i, (((![7, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (7 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_00_02_01
#print axioms Paper7MomentGapNumeric.valid_07_00_02_01

def qvalues_07_00_02_01 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_07_00_02_01

theorem row_07_00_02_01 : b4RowContribution (![7, 7, 9, 10] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![7, 7, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_07_00_02_01) :=
      sparseRow_sound (![7, 7, 9, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_07_00_02_01) valid_07_00_02_01
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_00_02_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_07_00_02_01

theorem weighted_07_00_02_01 : b4RawGapContribution ![7, 0, 2, 1] = 240 := by
  calc
    b4RawGapContribution ![7, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 20 :=
      b4GapContribution_from_row 7 0 2 1 20 row_07_00_02_01
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_01

theorem row_07_00_02_02 : b4RowContribution (![7, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 9, 11] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 9 + 11 = 34
    decide
  have hzsq : (∑ i, (((![7, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_02_02

theorem weighted_07_00_02_02 : b4RawGapContribution ![7, 0, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 0 :=
      b4GapContribution_from_row 7 0 2 2 0 row_07_00_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_02

theorem row_07_00_02_03 : b4RowContribution (![7, 7, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 9, 12] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 9 + 12 = 35
    decide
  have hzsq : (∑ i, (((![7, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_02_03

theorem weighted_07_00_02_03 : b4RawGapContribution ![7, 0, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 0 :=
      b4GapContribution_from_row 7 0 2 3 0 row_07_00_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_03

theorem row_07_00_02_04 : b4RowContribution (![7, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 9, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 9 + 13 = 36
    decide
  have hzsq : (∑ i, (((![7, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_02_04

theorem weighted_07_00_02_04 : b4RawGapContribution ![7, 0, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 0 :=
      b4GapContribution_from_row 7 0 2 4 0 row_07_00_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_04

theorem row_07_00_02_05 : b4RowContribution (![7, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 9, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 9 + 14 = 37
    decide
  have hzsq : (∑ i, (((![7, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_02_05

theorem weighted_07_00_02_05 : b4RawGapContribution ![7, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 7 0 2 5 0 row_07_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_02_05

def dvalues_07_00_02 : Fin 6 → ℕ := ![0, 240, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_00_02

theorem dblock_07_00_02 : b4GapPatternDBlock 7 0 2 = 240 := by
  calc
    b4GapPatternDBlock 7 0 2 = ∑ d : Fin 6, dvalues_07_00_02 d := by
      apply b4GapDBlock_of_rows 7 0 2 dvalues_07_00_02
      intro d
      fin_cases d
      · exact weighted_07_00_02_00
      · exact weighted_07_00_02_01
      · exact weighted_07_00_02_02
      · exact weighted_07_00_02_03
      · exact weighted_07_00_02_04
      · exact weighted_07_00_02_05
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_00_02

end Paper7MomentGapNumeric
