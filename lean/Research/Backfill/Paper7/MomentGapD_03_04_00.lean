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

theorem row_03_04_00_00 : b4RowContribution (![3, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 7] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 7 = 24
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 156 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 156
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_00

theorem weighted_03_04_00_00 : b4RawGapContribution ![3, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 3 4 0 0 0 row_03_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_00

theorem row_03_04_00_01 : b4RowContribution (![3, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 8] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 8 = 25
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_01

theorem weighted_03_04_00_01 : b4RawGapContribution ![3, 4, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 0 :=
      b4GapContribution_from_row 3 4 0 1 0 row_03_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_01

theorem row_03_04_00_02 : b4RowContribution (![3, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 9 = 26
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 188
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_02

theorem weighted_03_04_00_02 : b4RawGapContribution ![3, 4, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 2] = b4GapPatternWeight 4 0 2 * 0 :=
      b4GapContribution_from_row 3 4 0 2 0 row_03_04_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_02

theorem row_03_04_00_03 : b4RowContribution (![3, 7, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 10 = 27
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_03

theorem weighted_03_04_00_03 : b4RawGapContribution ![3, 4, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 3] = b4GapPatternWeight 4 0 3 * 0 :=
      b4GapContribution_from_row 3 4 0 3 0 row_03_04_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_03

def layers_03_04_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 28, 28, 26, 22, 18, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 52, 74, 100, 128, 156, 182, 204, 221, 232, 236, 232, 221, 204, 182]]
#print axioms Paper7MomentGapNumeric.layers_03_04_00_04

theorem cells_03_04_00_04 : QTableValid (![3, 7, 7, 11] : Fin 4 → ℕ) layers_03_04_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_04_00_04

theorem valid_03_04_00_04 :
    SparseRowValid (![3, 7, 7, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_04_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 7, 7, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 7 + 7 + 11 = 28
      decide
    have hzsq : (∑ i, (((![3, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_04_00_04
#print axioms Paper7MomentGapNumeric.valid_03_04_00_04

def qvalues_03_04_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 74, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_04_00_04

theorem row_03_04_00_04 : b4RowContribution (![3, 7, 7, 11] : Fin 4 → ℕ) = 74 := by
  calc
    b4RowContribution (![3, 7, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_03_04_00_04) :=
      sparseRow_sound (![3, 7, 7, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_04_00_04) valid_03_04_00_04
    _ = 74 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_04_00_04 Q := by
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
        _ = 74 := by decide
#print axioms Paper7MomentGapNumeric.row_03_04_00_04

theorem weighted_03_04_00_04 : b4RawGapContribution ![3, 4, 0, 4] = 888 := by
  calc
    b4RawGapContribution ![3, 4, 0, 4] = b4GapPatternWeight 4 0 4 * 74 :=
      b4GapContribution_from_row 3 4 0 4 74 row_03_04_00_04
    _ = 888 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_04

theorem row_03_04_00_05 : b4RowContribution (![3, 7, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 12 = 29
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_05

theorem weighted_03_04_00_05 : b4RawGapContribution ![3, 4, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 5] = b4GapPatternWeight 4 0 5 * 0 :=
      b4GapContribution_from_row 3 4 0 5 0 row_03_04_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_05

def layers_03_04_00_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 28, 28, 26, 22, 18, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 52, 74, 100, 128, 156, 182, 204, 222, 236, 245, 248, 245, 236, 222]]
#print axioms Paper7MomentGapNumeric.layers_03_04_00_06

theorem cells_03_04_00_06 : QTableValid (![3, 7, 7, 13] : Fin 4 → ℕ) layers_03_04_00_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_04_00_06

theorem valid_03_04_00_06 :
    SparseRowValid (![3, 7, 7, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_04_00_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 7, 7, 13] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 3 + 7 + 7 + 13 = 30
      decide
    have hzsq : (∑ i, (((![3, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_04_00_06
#print axioms Paper7MomentGapNumeric.valid_03_04_00_06

def qvalues_03_04_00_06 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_04_00_06

theorem row_03_04_00_06 : b4RowContribution (![3, 7, 7, 13] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![3, 7, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_03_04_00_06) :=
      sparseRow_sound (![3, 7, 7, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_04_00_06) valid_03_04_00_06
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_04_00_06 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_04_00_06

theorem weighted_03_04_00_06 : b4RawGapContribution ![3, 4, 0, 6] = 240 := by
  calc
    b4RawGapContribution ![3, 4, 0, 6] = b4GapPatternWeight 4 0 6 * 20 :=
      b4GapContribution_from_row 3 4 0 6 20 row_03_04_00_06
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_06

theorem row_03_04_00_07 : b4RowContribution (![3, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 14 = 31
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_07

theorem weighted_03_04_00_07 : b4RawGapContribution ![3, 4, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 7] = b4GapPatternWeight 4 0 7 * 0 :=
      b4GapContribution_from_row 3 4 0 7 0 row_03_04_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_07

theorem row_03_04_00_08 : b4RowContribution (![3, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 15 = 32
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_08

theorem weighted_03_04_00_08 : b4RawGapContribution ![3, 4, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 8] = b4GapPatternWeight 4 0 8 * 0 :=
      b4GapContribution_from_row 3 4 0 8 0 row_03_04_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_08

theorem row_03_04_00_09 : b4RowContribution (![3, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 16 = 33
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_09

theorem weighted_03_04_00_09 : b4RawGapContribution ![3, 4, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 9] = b4GapPatternWeight 4 0 9 * 0 :=
      b4GapContribution_from_row 3 4 0 9 0 row_03_04_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_09

theorem row_03_04_00_10 : b4RowContribution (![3, 7, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 17 = 34
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 17^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_10

theorem weighted_03_04_00_10 : b4RawGapContribution ![3, 4, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 10] = b4GapPatternWeight 4 0 10 * 0 :=
      b4GapContribution_from_row 3 4 0 10 0 row_03_04_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_10

theorem row_03_04_00_11 : b4RowContribution (![3, 7, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 18 = 35
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 431 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 18^2 = 431
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_11

theorem weighted_03_04_00_11 : b4RawGapContribution ![3, 4, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 11] = b4GapPatternWeight 4 0 11 * 0 :=
      b4GapContribution_from_row 3 4 0 11 0 row_03_04_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_11

theorem row_03_04_00_12 : b4RowContribution (![3, 7, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 19 = 36
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 19^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_12

theorem weighted_03_04_00_12 : b4RawGapContribution ![3, 4, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 12] = b4GapPatternWeight 4 0 12 * 0 :=
      b4GapContribution_from_row 3 4 0 12 0 row_03_04_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_12

theorem row_03_04_00_13 : b4RowContribution (![3, 7, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 7, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 7 + 20 = 37
    decide
  have hzsq : (∑ i, (((![3, 7, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 7^2 + 20^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_00_13

theorem weighted_03_04_00_13 : b4RawGapContribution ![3, 4, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 0, 13] = b4GapPatternWeight 4 0 13 * 0 :=
      b4GapContribution_from_row 3 4 0 13 0 row_03_04_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_00_13

def dvalues_03_04_00 : Fin 14 → ℕ := ![0, 0, 0, 0, 888, 0, 240, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_04_00

theorem dblock_03_04_00 : b4GapPatternDBlock 3 4 0 = 1128 := by
  calc
    b4GapPatternDBlock 3 4 0 = ∑ d : Fin 14, dvalues_03_04_00 d := by
      apply b4GapDBlock_of_rows 3 4 0 dvalues_03_04_00
      intro d
      fin_cases d
      · exact weighted_03_04_00_00
      · exact weighted_03_04_00_01
      · exact weighted_03_04_00_02
      · exact weighted_03_04_00_03
      · exact weighted_03_04_00_04
      · exact weighted_03_04_00_05
      · exact weighted_03_04_00_06
      · exact weighted_03_04_00_07
      · exact weighted_03_04_00_08
      · exact weighted_03_04_00_09
      · exact weighted_03_04_00_10
      · exact weighted_03_04_00_11
      · exact weighted_03_04_00_12
      · exact weighted_03_04_00_13
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_04_00

end Paper7MomentGapNumeric
