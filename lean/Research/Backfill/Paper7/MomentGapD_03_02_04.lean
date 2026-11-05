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

theorem row_03_02_04_00 : b4RowContribution (![3, 5, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 9 = 26
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 9^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_00

theorem weighted_03_02_04_00 : b4RawGapContribution ![3, 2, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 0] = b4GapPatternWeight 2 4 0 * 0 :=
      b4GapContribution_from_row 3 2 4 0 0 row_03_02_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_00

theorem row_03_02_04_01 : b4RowContribution (![3, 5, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 10 = 27
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 10^2 = 215
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_01

theorem weighted_03_02_04_01 : b4RawGapContribution ![3, 2, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 1] = b4GapPatternWeight 2 4 1 * 0 :=
      b4GapContribution_from_row 3 2 4 1 0 row_03_02_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_01

def layers_03_02_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 24, 24, 23, 21, 18, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 52, 73, 96, 120, 144, 167, 188, 205, 216, 220, 216, 205, 188, 167]]
#print axioms Paper7MomentGapNumeric.layers_03_02_04_02

theorem cells_03_02_04_02 : QTableValid (![3, 5, 9, 11] : Fin 4 → ℕ) layers_03_02_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_04_02

theorem valid_03_02_04_02 :
    SparseRowValid (![3, 5, 9, 11] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_02_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 9, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 9 + 11 = 28
      decide
    have hzsq : (∑ i, (((![3, 5, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 9^2 + 11^2 = 236
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_04_02
#print axioms Paper7MomentGapNumeric.valid_03_02_04_02

def qvalues_03_02_04_02 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_04_02

theorem row_03_02_04_02 : b4RowContribution (![3, 5, 9, 11] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![3, 5, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_03_02_04_02) :=
      sparseRow_sound (![3, 5, 9, 11] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_02_04_02) valid_03_02_04_02
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_04_02 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_04_02

theorem weighted_03_02_04_02 : b4RawGapContribution ![3, 2, 4, 2] = 240 := by
  calc
    b4RawGapContribution ![3, 2, 4, 2] = b4GapPatternWeight 2 4 2 * 10 :=
      b4GapContribution_from_row 3 2 4 2 10 row_03_02_04_02
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_02

theorem row_03_02_04_03 : b4RowContribution (![3, 5, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 12 = 29
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 12^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_03

theorem weighted_03_02_04_03 : b4RawGapContribution ![3, 2, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 3] = b4GapPatternWeight 2 4 3 * 0 :=
      b4GapContribution_from_row 3 2 4 3 0 row_03_02_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_03

def layers_03_02_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 24, 24, 23, 21, 18, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 52, 73, 96, 120, 144, 167, 188, 206, 220, 229, 232, 229, 220, 206]]
#print axioms Paper7MomentGapNumeric.layers_03_02_04_04

theorem cells_03_02_04_04 : QTableValid (![3, 5, 9, 13] : Fin 4 → ℕ) layers_03_02_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_04_04

theorem valid_03_02_04_04 :
    SparseRowValid (![3, 5, 9, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_02_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 9, 13] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 9 + 13 = 30
      decide
    have hzsq : (∑ i, (((![3, 5, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 9^2 + 13^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_04_04
#print axioms Paper7MomentGapNumeric.valid_03_02_04_04

def qvalues_03_02_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_04_04

theorem row_03_02_04_04 : b4RowContribution (![3, 5, 9, 13] : Fin 4 → ℕ) = 52 := by
  calc
    b4RowContribution (![3, 5, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_02_04_04) :=
      sparseRow_sound (![3, 5, 9, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_02_04_04) valid_03_02_04_04
    _ = 52 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_04_04 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 52 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_04_04

theorem weighted_03_02_04_04 : b4RawGapContribution ![3, 2, 4, 4] = 1248 := by
  calc
    b4RawGapContribution ![3, 2, 4, 4] = b4GapPatternWeight 2 4 4 * 52 :=
      b4GapContribution_from_row 3 2 4 4 52 row_03_02_04_04
    _ = 1248 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_04

theorem row_03_02_04_05 : b4RowContribution (![3, 5, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 14 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 14^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_05

theorem weighted_03_02_04_05 : b4RawGapContribution ![3, 2, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 5] = b4GapPatternWeight 2 4 5 * 0 :=
      b4GapContribution_from_row 3 2 4 5 0 row_03_02_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_05

theorem row_03_02_04_06 : b4RowContribution (![3, 5, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 15 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 15^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_06

theorem weighted_03_02_04_06 : b4RawGapContribution ![3, 2, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 6] = b4GapPatternWeight 2 4 6 * 0 :=
      b4GapContribution_from_row 3 2 4 6 0 row_03_02_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_06

theorem row_03_02_04_07 : b4RowContribution (![3, 5, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 16 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 16^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_07

theorem weighted_03_02_04_07 : b4RawGapContribution ![3, 2, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 7] = b4GapPatternWeight 2 4 7 * 0 :=
      b4GapContribution_from_row 3 2 4 7 0 row_03_02_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_07

theorem row_03_02_04_08 : b4RowContribution (![3, 5, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 17 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 17^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_08

theorem weighted_03_02_04_08 : b4RawGapContribution ![3, 2, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 8] = b4GapPatternWeight 2 4 8 * 0 :=
      b4GapContribution_from_row 3 2 4 8 0 row_03_02_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_08

theorem row_03_02_04_09 : b4RowContribution (![3, 5, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 18 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 439 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 18^2 = 439
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_09

theorem weighted_03_02_04_09 : b4RawGapContribution ![3, 2, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 9] = b4GapPatternWeight 2 4 9 * 0 :=
      b4GapContribution_from_row 3 2 4 9 0 row_03_02_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_09

theorem row_03_02_04_10 : b4RowContribution (![3, 5, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 19 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 476 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 19^2 = 476
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_10

theorem weighted_03_02_04_10 : b4RawGapContribution ![3, 2, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 10] = b4GapPatternWeight 2 4 10 * 0 :=
      b4GapContribution_from_row 3 2 4 10 0 row_03_02_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_10

theorem row_03_02_04_11 : b4RowContribution (![3, 5, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 9, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 9 + 20 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 515 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 9^2 + 20^2 = 515
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_04_11

theorem weighted_03_02_04_11 : b4RawGapContribution ![3, 2, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 4, 11] = b4GapPatternWeight 2 4 11 * 0 :=
      b4GapContribution_from_row 3 2 4 11 0 row_03_02_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_04_11

def dvalues_03_02_04 : Fin 12 → ℕ := ![0, 0, 240, 0, 1248, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_04

theorem dblock_03_02_04 : b4GapPatternDBlock 3 2 4 = 1488 := by
  calc
    b4GapPatternDBlock 3 2 4 = ∑ d : Fin 12, dvalues_03_02_04 d := by
      apply b4GapDBlock_of_rows 3 2 4 dvalues_03_02_04
      intro d
      fin_cases d
      · exact weighted_03_02_04_00
      · exact weighted_03_02_04_01
      · exact weighted_03_02_04_02
      · exact weighted_03_02_04_03
      · exact weighted_03_02_04_04
      · exact weighted_03_02_04_05
      · exact weighted_03_02_04_06
      · exact weighted_03_02_04_07
      · exact weighted_03_02_04_08
      · exact weighted_03_02_04_09
      · exact weighted_03_02_04_10
      · exact weighted_03_02_04_11
    _ = 1488 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_04

end Paper7MomentGapNumeric
