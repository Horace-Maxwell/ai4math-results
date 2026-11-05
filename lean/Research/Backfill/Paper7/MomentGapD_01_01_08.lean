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

theorem row_01_01_08_00 : b4RowContribution (![1, 2, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 10 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 10^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_00

theorem weighted_01_01_08_00 : b4RawGapContribution ![1, 1, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 0] = b4GapPatternWeight 1 8 0 * 0 :=
      b4GapContribution_from_row 1 1 8 0 0 row_01_01_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_00

def layers_01_01_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 57, 62, 64, 62, 57, 51, 45, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_01_01_08_01

theorem cells_01_01_08_01 : QTableValid (![1, 2, 10, 11] : Fin 4 → ℕ) layers_01_01_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_08_01

theorem valid_01_01_08_01 :
    SparseRowValid (![1, 2, 10, 11] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 10, 11] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 10 + 11 = 24
      decide
    have hzsq : (∑ i, (((![1, 2, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 10^2 + 11^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_08_01
#print axioms Paper7MomentGapNumeric.valid_01_01_08_01

def qvalues_01_01_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 62, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_08_01

theorem row_01_01_08_01 : b4RowContribution (![1, 2, 10, 11] : Fin 4 → ℕ) = 101 := by
  calc
    b4RowContribution (![1, 2, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_08_01) :=
      sparseRow_sound (![1, 2, 10, 11] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_08_01) valid_01_01_08_01
    _ = 101 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_08_01 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
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
        _ = 101 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_08_01

theorem weighted_01_01_08_01 : b4RawGapContribution ![1, 1, 8, 1] = 2424 := by
  calc
    b4RawGapContribution ![1, 1, 8, 1] = b4GapPatternWeight 1 8 1 * 101 :=
      b4GapContribution_from_row 1 1 8 1 101 row_01_01_08_01
    _ = 2424 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_01

theorem row_01_01_08_02 : b4RowContribution (![1, 2, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 12 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 12^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_02

theorem weighted_01_01_08_02 : b4RawGapContribution ![1, 1, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 2] = b4GapPatternWeight 1 8 2 * 0 :=
      b4GapContribution_from_row 1 1 8 2 0 row_01_01_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_02

def layers_01_01_08_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 57, 62, 65, 66, 65, 62, 57, 51, 45]]
#print axioms Paper7MomentGapNumeric.layers_01_01_08_03

theorem cells_01_01_08_03 : QTableValid (![1, 2, 10, 13] : Fin 4 → ℕ) layers_01_01_08_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_08_03

theorem valid_01_01_08_03 :
    SparseRowValid (![1, 2, 10, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_08_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 10, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 10 + 13 = 26
      decide
    have hzsq : (∑ i, (((![1, 2, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 10^2 + 13^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_08_03
#print axioms Paper7MomentGapNumeric.valid_01_01_08_03

def qvalues_01_01_08_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_08_03

theorem row_01_01_08_03 : b4RowContribution (![1, 2, 10, 13] : Fin 4 → ℕ) = 57 := by
  calc
    b4RowContribution (![1, 2, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_01_08_03) :=
      sparseRow_sound (![1, 2, 10, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_08_03) valid_01_01_08_03
    _ = 57 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_08_03 Q := by
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
        _ = 57 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_08_03

theorem weighted_01_01_08_03 : b4RawGapContribution ![1, 1, 8, 3] = 1368 := by
  calc
    b4RawGapContribution ![1, 1, 8, 3] = b4GapPatternWeight 1 8 3 * 57 :=
      b4GapContribution_from_row 1 1 8 3 57 row_01_01_08_03
    _ = 1368 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_03

theorem row_01_01_08_04 : b4RowContribution (![1, 2, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 14 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 14^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_04

theorem weighted_01_01_08_04 : b4RawGapContribution ![1, 1, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 4] = b4GapPatternWeight 1 8 4 * 0 :=
      b4GapContribution_from_row 1 1 8 4 0 row_01_01_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_04

theorem row_01_01_08_05 : b4RowContribution (![1, 2, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 15^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_05

theorem weighted_01_01_08_05 : b4RawGapContribution ![1, 1, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 5] = b4GapPatternWeight 1 8 5 * 0 :=
      b4GapContribution_from_row 1 1 8 5 0 row_01_01_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_05

theorem row_01_01_08_06 : b4RowContribution (![1, 2, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 16^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_06

theorem weighted_01_01_08_06 : b4RawGapContribution ![1, 1, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 6] = b4GapPatternWeight 1 8 6 * 0 :=
      b4GapContribution_from_row 1 1 8 6 0 row_01_01_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_06

theorem row_01_01_08_07 : b4RowContribution (![1, 2, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 17^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_07

theorem weighted_01_01_08_07 : b4RawGapContribution ![1, 1, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 7] = b4GapPatternWeight 1 8 7 * 0 :=
      b4GapContribution_from_row 1 1 8 7 0 row_01_01_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_07

theorem row_01_01_08_08 : b4RowContribution (![1, 2, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 18^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_08

theorem weighted_01_01_08_08 : b4RawGapContribution ![1, 1, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 8] = b4GapPatternWeight 1 8 8 * 0 :=
      b4GapContribution_from_row 1 1 8 8 0 row_01_01_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_08

theorem row_01_01_08_09 : b4RowContribution (![1, 2, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 466 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 19^2 = 466
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_09

theorem weighted_01_01_08_09 : b4RawGapContribution ![1, 1, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 9] = b4GapPatternWeight 1 8 9 * 0 :=
      b4GapContribution_from_row 1 1 8 9 0 row_01_01_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_09

theorem row_01_01_08_10 : b4RowContribution (![1, 2, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 20^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_10

theorem weighted_01_01_08_10 : b4RawGapContribution ![1, 1, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 10] = b4GapPatternWeight 1 8 10 * 0 :=
      b4GapContribution_from_row 1 1 8 10 0 row_01_01_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_10

theorem row_01_01_08_11 : b4RowContribution (![1, 2, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 21 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 21^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_11

theorem weighted_01_01_08_11 : b4RawGapContribution ![1, 1, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 11] = b4GapPatternWeight 1 8 11 * 0 :=
      b4GapContribution_from_row 1 1 8 11 0 row_01_01_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_11

theorem row_01_01_08_12 : b4RowContribution (![1, 2, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 22 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 589 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 22^2 = 589
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_12

theorem weighted_01_01_08_12 : b4RawGapContribution ![1, 1, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 12] = b4GapPatternWeight 1 8 12 * 0 :=
      b4GapContribution_from_row 1 1 8 12 0 row_01_01_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_12

theorem row_01_01_08_13 : b4RowContribution (![1, 2, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 634 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 23^2 = 634
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_13

theorem weighted_01_01_08_13 : b4RawGapContribution ![1, 1, 8, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 13] = b4GapPatternWeight 1 8 13 * 0 :=
      b4GapContribution_from_row 1 1 8 13 0 row_01_01_08_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_13

theorem row_01_01_08_14 : b4RowContribution (![1, 2, 10, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 10, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 10 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 681 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 10^2 + 24^2 = 681
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_08_14

theorem weighted_01_01_08_14 : b4RawGapContribution ![1, 1, 8, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 8, 14] = b4GapPatternWeight 1 8 14 * 0 :=
      b4GapContribution_from_row 1 1 8 14 0 row_01_01_08_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_08_14

def dvalues_01_01_08 : Fin 15 → ℕ := ![0, 2424, 0, 1368, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_08

theorem dblock_01_01_08 : b4GapPatternDBlock 1 1 8 = 3792 := by
  calc
    b4GapPatternDBlock 1 1 8 = ∑ d : Fin 15, dvalues_01_01_08 d := by
      apply b4GapDBlock_of_rows 1 1 8 dvalues_01_01_08
      intro d
      fin_cases d
      · exact weighted_01_01_08_00
      · exact weighted_01_01_08_01
      · exact weighted_01_01_08_02
      · exact weighted_01_01_08_03
      · exact weighted_01_01_08_04
      · exact weighted_01_01_08_05
      · exact weighted_01_01_08_06
      · exact weighted_01_01_08_07
      · exact weighted_01_01_08_08
      · exact weighted_01_01_08_09
      · exact weighted_01_01_08_10
      · exact weighted_01_01_08_11
      · exact weighted_01_01_08_12
      · exact weighted_01_01_08_13
      · exact weighted_01_01_08_14
    _ = 3792 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_08

end Paper7MomentGapNumeric
