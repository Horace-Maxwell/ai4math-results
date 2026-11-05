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

theorem row_02_04_02_00 : b4RowContribution (![2, 6, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 8 = 24
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 168 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 8^2 = 168
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_00

theorem weighted_02_04_02_00 : b4RawGapContribution ![2, 4, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 0] = b4GapPatternWeight 4 2 0 * 0 :=
      b4GapContribution_from_row 2 4 2 0 0 row_02_04_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_00

theorem row_02_04_02_01 : b4RowContribution (![2, 6, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 9 = 25
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 9^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_01

theorem weighted_02_04_02_01 : b4RawGapContribution ![2, 4, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 1] = b4GapPatternWeight 4 2 1 * 0 :=
      b4GapContribution_from_row 2 4 2 1 0 row_02_04_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_01

theorem row_02_04_02_02 : b4RowContribution (![2, 6, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 10 = 26
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 10^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_02

theorem weighted_02_04_02_02 : b4RawGapContribution ![2, 4, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 2] = b4GapPatternWeight 4 2 2 * 0 :=
      b4GapContribution_from_row 2 4 2 2 0 row_02_04_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_02

def layers_02_04_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 20, 18, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 84, 105, 125, 143, 158, 169, 175, 175, 169, 158, 143, 125]]
#print axioms Paper7MomentGapNumeric.layers_02_04_02_03

theorem cells_02_04_02_03 : QTableValid (![2, 6, 8, 11] : Fin 4 → ℕ) layers_02_04_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_02_03

theorem valid_02_04_02_03 :
    SparseRowValid (![2, 6, 8, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_04_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 8, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 8 + 11 = 27
      decide
    have hzsq : (∑ i, (((![2, 6, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 8^2 + 11^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_02_03
#print axioms Paper7MomentGapNumeric.valid_02_04_02_03

def qvalues_02_04_02_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_02_03

theorem row_02_04_02_03 : b4RowContribution (![2, 6, 8, 11] : Fin 4 → ℕ) = 125 := by
  calc
    b4RowContribution (![2, 6, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_04_02_03) :=
      sparseRow_sound (![2, 6, 8, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_04_02_03) valid_02_04_02_03
    _ = 125 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_02_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 125 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_02_03

theorem weighted_02_04_02_03 : b4RawGapContribution ![2, 4, 2, 3] = 3000 := by
  calc
    b4RawGapContribution ![2, 4, 2, 3] = b4GapPatternWeight 4 2 3 * 125 :=
      b4GapContribution_from_row 2 4 2 3 125 row_02_04_02_03
    _ = 3000 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_03

theorem row_02_04_02_04 : b4RowContribution (![2, 6, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 12 = 28
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 248 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 12^2 = 248
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_04

theorem weighted_02_04_02_04 : b4RawGapContribution ![2, 4, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 4] = b4GapPatternWeight 4 2 4 * 0 :=
      b4GapContribution_from_row 2 4 2 4 0 row_02_04_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_04

def layers_02_04_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 20, 18, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 84, 105, 125, 143, 158, 170, 179, 184, 184, 179, 170, 158]]
#print axioms Paper7MomentGapNumeric.layers_02_04_02_05

theorem cells_02_04_02_05 : QTableValid (![2, 6, 8, 13] : Fin 4 → ℕ) layers_02_04_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_02_05

theorem valid_02_04_02_05 :
    SparseRowValid (![2, 6, 8, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_04_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 8, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 8 + 13 = 29
      decide
    have hzsq : (∑ i, (((![2, 6, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 8^2 + 13^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_02_05
#print axioms Paper7MomentGapNumeric.valid_02_04_02_05

def qvalues_02_04_02_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_02_05

theorem row_02_04_02_05 : b4RowContribution (![2, 6, 8, 13] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![2, 6, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_04_02_05) :=
      sparseRow_sound (![2, 6, 8, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_04_02_05) valid_02_04_02_05
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_02_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_02_05

theorem weighted_02_04_02_05 : b4RawGapContribution ![2, 4, 2, 5] = 1536 := by
  calc
    b4RawGapContribution ![2, 4, 2, 5] = b4GapPatternWeight 4 2 5 * 64 :=
      b4GapContribution_from_row 2 4 2 5 64 row_02_04_02_05
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_05

theorem row_02_04_02_06 : b4RowContribution (![2, 6, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 14 = 30
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 14^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_06

theorem weighted_02_04_02_06 : b4RawGapContribution ![2, 4, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 6] = b4GapPatternWeight 4 2 6 * 0 :=
      b4GapContribution_from_row 2 4 2 6 0 row_02_04_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_06

theorem row_02_04_02_07 : b4RowContribution (![2, 6, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 15 = 31
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 15^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_07

theorem weighted_02_04_02_07 : b4RawGapContribution ![2, 4, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 7] = b4GapPatternWeight 4 2 7 * 0 :=
      b4GapContribution_from_row 2 4 2 7 0 row_02_04_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_07

theorem row_02_04_02_08 : b4RowContribution (![2, 6, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 16 = 32
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 16^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_08

theorem weighted_02_04_02_08 : b4RawGapContribution ![2, 4, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 8] = b4GapPatternWeight 4 2 8 * 0 :=
      b4GapContribution_from_row 2 4 2 8 0 row_02_04_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_08

theorem row_02_04_02_09 : b4RowContribution (![2, 6, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 17 = 33
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 17^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_09

theorem weighted_02_04_02_09 : b4RawGapContribution ![2, 4, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 9] = b4GapPatternWeight 4 2 9 * 0 :=
      b4GapContribution_from_row 2 4 2 9 0 row_02_04_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_09

theorem row_02_04_02_10 : b4RowContribution (![2, 6, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 18 = 34
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 18^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_10

theorem weighted_02_04_02_10 : b4RawGapContribution ![2, 4, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 10] = b4GapPatternWeight 4 2 10 * 0 :=
      b4GapContribution_from_row 2 4 2 10 0 row_02_04_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_10

theorem row_02_04_02_11 : b4RowContribution (![2, 6, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 19 = 35
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 19^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_11

theorem weighted_02_04_02_11 : b4RawGapContribution ![2, 4, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 11] = b4GapPatternWeight 4 2 11 * 0 :=
      b4GapContribution_from_row 2 4 2 11 0 row_02_04_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_11

theorem row_02_04_02_12 : b4RowContribution (![2, 6, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 20 = 36
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 504 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 20^2 = 504
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_12

theorem weighted_02_04_02_12 : b4RawGapContribution ![2, 4, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 12] = b4GapPatternWeight 4 2 12 * 0 :=
      b4GapContribution_from_row 2 4 2 12 0 row_02_04_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_12

theorem row_02_04_02_13 : b4RowContribution (![2, 6, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 8, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 8 + 21 = 37
    decide
  have hzsq : (∑ i, (((![2, 6, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 545 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 8^2 + 21^2 = 545
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_02_13

theorem weighted_02_04_02_13 : b4RawGapContribution ![2, 4, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 2, 13] = b4GapPatternWeight 4 2 13 * 0 :=
      b4GapContribution_from_row 2 4 2 13 0 row_02_04_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_02_13

def dvalues_02_04_02 : Fin 14 → ℕ := ![0, 0, 0, 3000, 0, 1536, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_04_02

theorem dblock_02_04_02 : b4GapPatternDBlock 2 4 2 = 4536 := by
  calc
    b4GapPatternDBlock 2 4 2 = ∑ d : Fin 14, dvalues_02_04_02 d := by
      apply b4GapDBlock_of_rows 2 4 2 dvalues_02_04_02
      intro d
      fin_cases d
      · exact weighted_02_04_02_00
      · exact weighted_02_04_02_01
      · exact weighted_02_04_02_02
      · exact weighted_02_04_02_03
      · exact weighted_02_04_02_04
      · exact weighted_02_04_02_05
      · exact weighted_02_04_02_06
      · exact weighted_02_04_02_07
      · exact weighted_02_04_02_08
      · exact weighted_02_04_02_09
      · exact weighted_02_04_02_10
      · exact weighted_02_04_02_11
      · exact weighted_02_04_02_12
      · exact weighted_02_04_02_13
    _ = 4536 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_04_02

end Paper7MomentGapNumeric
