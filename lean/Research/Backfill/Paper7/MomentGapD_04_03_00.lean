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

theorem row_04_03_00_00 : b4RowContribution (![4, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 7] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 7 = 25
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 163
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_00

theorem weighted_04_03_00_00 : b4RawGapContribution ![4, 3, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 0] = b4GapPatternWeight 3 0 0 * 0 :=
      b4GapContribution_from_row 4 3 0 0 0 row_04_03_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_00

theorem row_04_03_00_01 : b4RowContribution (![4, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 8 = 26
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_01

theorem weighted_04_03_00_01 : b4RawGapContribution ![4, 3, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 1] = b4GapPatternWeight 3 0 1 * 0 :=
      b4GapContribution_from_row 4 3 0 1 0 row_04_03_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_01

theorem row_04_03_00_02 : b4RowContribution (![4, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 9 = 27
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_02

theorem weighted_04_03_00_02 : b4RawGapContribution ![4, 3, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 2] = b4GapPatternWeight 3 0 2 * 0 :=
      b4GapContribution_from_row 4 3 0 2 0 row_04_03_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_02

theorem row_04_03_00_03 : b4RowContribution (![4, 7, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 10 = 28
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 214
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_03

theorem weighted_04_03_00_03 : b4RawGapContribution ![4, 3, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 3] = b4GapPatternWeight 3 0 3 * 0 :=
      b4GapContribution_from_row 4 3 0 3 0 row_04_03_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_03

def layers_04_03_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 33, 34, 33, 30, 25, 20, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 55, 80, 110, 143, 177, 210, 240, 264, 281, 290, 290, 281, 264, 240]]
#print axioms Paper7MomentGapNumeric.layers_04_03_00_04

theorem cells_04_03_00_04 : QTableValid (![4, 7, 7, 11] : Fin 4 → ℕ) layers_04_03_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_03_00_04

theorem valid_04_03_00_04 :
    SparseRowValid (![4, 7, 7, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_04_03_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 7, 7, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 7 + 7 + 11 = 29
      decide
    have hzsq : (∑ i, (((![4, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_03_00_04
#print axioms Paper7MomentGapNumeric.valid_04_03_00_04

def qvalues_04_03_00_04 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_03_00_04

theorem row_04_03_00_04 : b4RowContribution (![4, 7, 7, 11] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![4, 7, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_04_03_00_04) :=
      sparseRow_sound (![4, 7, 7, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_04_03_00_04) valid_04_03_00_04
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_03_00_04 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_04_03_00_04

theorem weighted_04_03_00_04 : b4RawGapContribution ![4, 3, 0, 4] = 48 := by
  calc
    b4RawGapContribution ![4, 3, 0, 4] = b4GapPatternWeight 3 0 4 * 4 :=
      b4GapContribution_from_row 4 3 0 4 4 row_04_03_00_04
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_04

theorem row_04_03_00_05 : b4RowContribution (![4, 7, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 12 = 30
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_05

theorem weighted_04_03_00_05 : b4RawGapContribution ![4, 3, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 5] = b4GapPatternWeight 3 0 5 * 0 :=
      b4GapContribution_from_row 4 3 0 5 0 row_04_03_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_05

def layers_04_03_00_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 33, 34, 33, 30, 25, 20, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 55, 80, 110, 143, 177, 210, 240, 265, 285, 299, 306, 306, 299, 285]]
#print axioms Paper7MomentGapNumeric.layers_04_03_00_06

theorem cells_04_03_00_06 : QTableValid (![4, 7, 7, 13] : Fin 4 → ℕ) layers_04_03_00_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_03_00_06

theorem valid_04_03_00_06 :
    SparseRowValid (![4, 7, 7, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_03_00_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 7, 7, 13] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 4 + 7 + 7 + 13 = 31
      decide
    have hzsq : (∑ i, (((![4, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_03_00_06
#print axioms Paper7MomentGapNumeric.valid_04_03_00_06

def qvalues_04_03_00_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_03_00_06

theorem row_04_03_00_06 : b4RowContribution (![4, 7, 7, 13] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 7, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_03_00_06) :=
      sparseRow_sound (![4, 7, 7, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_03_00_06) valid_04_03_00_06
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_03_00_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_04_03_00_06

theorem weighted_04_03_00_06 : b4RawGapContribution ![4, 3, 0, 6] = 420 := by
  calc
    b4RawGapContribution ![4, 3, 0, 6] = b4GapPatternWeight 3 0 6 * 35 :=
      b4GapContribution_from_row 4 3 0 6 35 row_04_03_00_06
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_06

theorem row_04_03_00_07 : b4RowContribution (![4, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 14 = 32
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_07

theorem weighted_04_03_00_07 : b4RawGapContribution ![4, 3, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 7] = b4GapPatternWeight 3 0 7 * 0 :=
      b4GapContribution_from_row 4 3 0 7 0 row_04_03_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_07

theorem row_04_03_00_08 : b4RowContribution (![4, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 15 = 33
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_08

theorem weighted_04_03_00_08 : b4RawGapContribution ![4, 3, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 8] = b4GapPatternWeight 3 0 8 * 0 :=
      b4GapContribution_from_row 4 3 0 8 0 row_04_03_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_08

theorem row_04_03_00_09 : b4RowContribution (![4, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 16 = 34
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_09

theorem weighted_04_03_00_09 : b4RawGapContribution ![4, 3, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 9] = b4GapPatternWeight 3 0 9 * 0 :=
      b4GapContribution_from_row 4 3 0 9 0 row_04_03_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_09

theorem row_04_03_00_10 : b4RowContribution (![4, 7, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 17 = 35
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 17^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_10

theorem weighted_04_03_00_10 : b4RawGapContribution ![4, 3, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 10] = b4GapPatternWeight 3 0 10 * 0 :=
      b4GapContribution_from_row 4 3 0 10 0 row_04_03_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_10

theorem row_04_03_00_11 : b4RowContribution (![4, 7, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 18 = 36
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 18^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_11

theorem weighted_04_03_00_11 : b4RawGapContribution ![4, 3, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 11] = b4GapPatternWeight 3 0 11 * 0 :=
      b4GapContribution_from_row 4 3 0 11 0 row_04_03_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_11

theorem row_04_03_00_12 : b4RowContribution (![4, 7, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 7, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 7 + 19 = 37
    decide
  have hzsq : (∑ i, (((![4, 7, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 7^2 + 19^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_00_12

theorem weighted_04_03_00_12 : b4RawGapContribution ![4, 3, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 0, 12] = b4GapPatternWeight 3 0 12 * 0 :=
      b4GapContribution_from_row 4 3 0 12 0 row_04_03_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_00_12

def dvalues_04_03_00 : Fin 13 → ℕ := ![0, 0, 0, 0, 48, 0, 420, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_03_00

theorem dblock_04_03_00 : b4GapPatternDBlock 4 3 0 = 468 := by
  calc
    b4GapPatternDBlock 4 3 0 = ∑ d : Fin 13, dvalues_04_03_00 d := by
      apply b4GapDBlock_of_rows 4 3 0 dvalues_04_03_00
      intro d
      fin_cases d
      · exact weighted_04_03_00_00
      · exact weighted_04_03_00_01
      · exact weighted_04_03_00_02
      · exact weighted_04_03_00_03
      · exact weighted_04_03_00_04
      · exact weighted_04_03_00_05
      · exact weighted_04_03_00_06
      · exact weighted_04_03_00_07
      · exact weighted_04_03_00_08
      · exact weighted_04_03_00_09
      · exact weighted_04_03_00_10
      · exact weighted_04_03_00_11
      · exact weighted_04_03_00_12
    _ = 468 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_03_00

end Paper7MomentGapNumeric
