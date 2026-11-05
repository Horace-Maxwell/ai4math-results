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

def layers_02_07_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 29, 29, 27, 24, 21, 18, 15, 12, 9], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 136, 165, 193, 217, 235, 247, 253, 253, 247, 235]]
#print axioms Paper7MomentGapNumeric.layers_02_07_01_00

theorem cells_02_07_01_00 : QTableValid (![2, 9, 10, 10] : Fin 4 → ℕ) layers_02_07_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_07_01_00

theorem valid_02_07_01_00 :
    SparseRowValid (![2, 9, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_07_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 9, 10, 10] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 2 + 9 + 10 + 10 = 31
      decide
    have hzsq : (∑ i, (((![2, 9, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 9^2 + 10^2 + 10^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_07_01_00
#print axioms Paper7MomentGapNumeric.valid_02_07_01_00

def qvalues_02_07_01_00 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_07_01_00

theorem row_02_07_01_00 : b4RowContribution (![2, 9, 10, 10] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![2, 9, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_07_01_00) :=
      sparseRow_sound (![2, 9, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_07_01_00) valid_02_07_01_00
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_07_01_00 Q := by
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
        _ = 19 := by decide
#print axioms Paper7MomentGapNumeric.row_02_07_01_00

theorem weighted_02_07_01_00 : b4RawGapContribution ![2, 7, 1, 0] = 228 := by
  calc
    b4RawGapContribution ![2, 7, 1, 0] = b4GapPatternWeight 7 1 0 * 19 :=
      b4GapContribution_from_row 2 7 1 0 19 row_02_07_01_00
    _ = 228 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_00

theorem row_02_07_01_01 : b4RowContribution (![2, 9, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 11 = 32
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 11^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_01

theorem weighted_02_07_01_01 : b4RawGapContribution ![2, 7, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 1] = b4GapPatternWeight 7 1 1 * 0 :=
      b4GapContribution_from_row 2 7 1 1 0 row_02_07_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_01

theorem row_02_07_01_02 : b4RowContribution (![2, 9, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 12 = 33
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 12^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_02

theorem weighted_02_07_01_02 : b4RawGapContribution ![2, 7, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 2] = b4GapPatternWeight 7 1 2 * 0 :=
      b4GapContribution_from_row 2 7 1 2 0 row_02_07_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_02

theorem row_02_07_01_03 : b4RowContribution (![2, 9, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 13 = 34
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 13^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_03

theorem weighted_02_07_01_03 : b4RawGapContribution ![2, 7, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 3] = b4GapPatternWeight 7 1 3 * 0 :=
      b4GapContribution_from_row 2 7 1 3 0 row_02_07_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_03

theorem row_02_07_01_04 : b4RowContribution (![2, 9, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 14 = 35
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 14^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_04

theorem weighted_02_07_01_04 : b4RawGapContribution ![2, 7, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 4] = b4GapPatternWeight 7 1 4 * 0 :=
      b4GapContribution_from_row 2 7 1 4 0 row_02_07_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_04

theorem row_02_07_01_05 : b4RowContribution (![2, 9, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 15 = 36
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 15^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_05

theorem weighted_02_07_01_05 : b4RawGapContribution ![2, 7, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 5] = b4GapPatternWeight 7 1 5 * 0 :=
      b4GapContribution_from_row 2 7 1 5 0 row_02_07_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_05

theorem row_02_07_01_06 : b4RowContribution (![2, 9, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 9, 10, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 9 + 10 + 16 = 37
    decide
  have hzsq : (∑ i, (((![2, 9, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 9^2 + 10^2 + 16^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_07_01_06

theorem weighted_02_07_01_06 : b4RawGapContribution ![2, 7, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 7, 1, 6] = b4GapPatternWeight 7 1 6 * 0 :=
      b4GapContribution_from_row 2 7 1 6 0 row_02_07_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_07_01_06

def dvalues_02_07_01 : Fin 7 → ℕ := ![228, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_07_01

theorem dblock_02_07_01 : b4GapPatternDBlock 2 7 1 = 228 := by
  calc
    b4GapPatternDBlock 2 7 1 = ∑ d : Fin 7, dvalues_02_07_01 d := by
      apply b4GapDBlock_of_rows 2 7 1 dvalues_02_07_01
      intro d
      fin_cases d
      · exact weighted_02_07_01_00
      · exact weighted_02_07_01_01
      · exact weighted_02_07_01_02
      · exact weighted_02_07_01_03
      · exact weighted_02_07_01_04
      · exact weighted_02_07_01_05
      · exact weighted_02_07_01_06
    _ = 228 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_07_01

end Paper7MomentGapNumeric
