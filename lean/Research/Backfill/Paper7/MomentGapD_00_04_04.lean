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

theorem row_00_04_04_00 : b4RowContribution (![0, 4, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 8 = 20
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 144 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 8^2 = 144
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_00

theorem weighted_00_04_04_00 : b4RawGapContribution ![0, 4, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 0] = b4GapPatternWeight 4 4 0 * 0 :=
      b4GapContribution_from_row 0 4 4 0 0 row_00_04_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_00

theorem row_00_04_04_01 : b4RowContribution (![0, 4, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 9 = 21
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 9^2 = 161
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_01

theorem weighted_00_04_04_01 : b4RawGapContribution ![0, 4, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 1] = b4GapPatternWeight 4 4 1 * 0 :=
      b4GapContribution_from_row 0 4 4 1 0 row_00_04_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_01

theorem row_00_04_04_02 : b4RowContribution (![0, 4, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 10 = 22
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 10^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_02

theorem weighted_00_04_04_02 : b4RawGapContribution ![0, 4, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 2] = b4GapPatternWeight 4 4 2 * 0 :=
      b4GapContribution_from_row 0 4 4 2 0 row_00_04_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_02

theorem row_00_04_04_03 : b4RowContribution (![0, 4, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 11 = 23
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 11^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_03

theorem weighted_00_04_04_03 : b4RawGapContribution ![0, 4, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 3] = b4GapPatternWeight 4 4 3 * 0 :=
      b4GapContribution_from_row 0 4 4 3 0 row_00_04_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_03

def layers_00_04_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 39, 42, 44, 45, 44, 42, 39, 35, 30, 25]]
#print axioms Paper7MomentGapNumeric.layers_00_04_04_04

theorem cells_00_04_04_04 : QTableValid (![0, 4, 8, 12] : Fin 4 → ℕ) layers_00_04_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_04_04

theorem valid_00_04_04_04 :
    SparseRowValid (![0, 4, 8, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 8, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 8 + 12 = 24
      decide
    have hzsq : (∑ i, (((![0, 4, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 224 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 8^2 + 12^2 = 224
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_04_04
#print axioms Paper7MomentGapNumeric.valid_00_04_04_04

def qvalues_00_04_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_04_04

theorem row_00_04_04_04 : b4RowContribution (![0, 4, 8, 12] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![0, 4, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_04_04_04) :=
      sparseRow_sound (![0, 4, 8, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_04_04) valid_00_04_04_04
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_04_04 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_04_04

theorem weighted_00_04_04_04 : b4RawGapContribution ![0, 4, 4, 4] = 840 := by
  calc
    b4RawGapContribution ![0, 4, 4, 4] = b4GapPatternWeight 4 4 4 * 35 :=
      b4GapContribution_from_row 0 4 4 4 35 row_00_04_04_04
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_04

theorem row_00_04_04_05 : b4RowContribution (![0, 4, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 13 = 25
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 13^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_05

theorem weighted_00_04_04_05 : b4RawGapContribution ![0, 4, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 5] = b4GapPatternWeight 4 4 5 * 0 :=
      b4GapContribution_from_row 0 4 4 5 0 row_00_04_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_05

def layers_00_04_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 39, 42, 44, 45, 45, 45, 44, 42, 39, 35]]
#print axioms Paper7MomentGapNumeric.layers_00_04_04_06

theorem cells_00_04_04_06 : QTableValid (![0, 4, 8, 14] : Fin 4 → ℕ) layers_00_04_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_04_06

theorem valid_00_04_04_06 :
    SparseRowValid (![0, 4, 8, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_04_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 8, 14] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 8 + 14 = 26
      decide
    have hzsq : (∑ i, (((![0, 4, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 8^2 + 14^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_04_06
#print axioms Paper7MomentGapNumeric.valid_00_04_04_06

def qvalues_00_04_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_04_06

theorem row_00_04_04_06 : b4RowContribution (![0, 4, 8, 14] : Fin 4 → ℕ) = 39 := by
  calc
    b4RowContribution (![0, 4, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_04_04_06) :=
      sparseRow_sound (![0, 4, 8, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_04_04_06) valid_00_04_04_06
    _ = 39 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_04_06 Q := by
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
        _ = 39 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_04_06

theorem weighted_00_04_04_06 : b4RawGapContribution ![0, 4, 4, 6] = 936 := by
  calc
    b4RawGapContribution ![0, 4, 4, 6] = b4GapPatternWeight 4 4 6 * 39 :=
      b4GapContribution_from_row 0 4 4 6 39 row_00_04_04_06
    _ = 936 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_06

theorem row_00_04_04_07 : b4RowContribution (![0, 4, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 15^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_07

theorem weighted_00_04_04_07 : b4RawGapContribution ![0, 4, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 7] = b4GapPatternWeight 4 4 7 * 0 :=
      b4GapContribution_from_row 0 4 4 7 0 row_00_04_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_07

theorem row_00_04_04_08 : b4RowContribution (![0, 4, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 336 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 16^2 = 336
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_08

theorem weighted_00_04_04_08 : b4RawGapContribution ![0, 4, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 8] = b4GapPatternWeight 4 4 8 * 0 :=
      b4GapContribution_from_row 0 4 4 8 0 row_00_04_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_08

theorem row_00_04_04_09 : b4RowContribution (![0, 4, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 17^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_09

theorem weighted_00_04_04_09 : b4RawGapContribution ![0, 4, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 9] = b4GapPatternWeight 4 4 9 * 0 :=
      b4GapContribution_from_row 0 4 4 9 0 row_00_04_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_09

theorem row_00_04_04_10 : b4RowContribution (![0, 4, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 18^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_10

theorem weighted_00_04_04_10 : b4RawGapContribution ![0, 4, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 10] = b4GapPatternWeight 4 4 10 * 0 :=
      b4GapContribution_from_row 0 4 4 10 0 row_00_04_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_10

theorem row_00_04_04_11 : b4RowContribution (![0, 4, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 19^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_11

theorem weighted_00_04_04_11 : b4RawGapContribution ![0, 4, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 11] = b4GapPatternWeight 4 4 11 * 0 :=
      b4GapContribution_from_row 0 4 4 11 0 row_00_04_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_11

theorem row_00_04_04_12 : b4RowContribution (![0, 4, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 480 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 20^2 = 480
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_12

theorem weighted_00_04_04_12 : b4RawGapContribution ![0, 4, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 12] = b4GapPatternWeight 4 4 12 * 0 :=
      b4GapContribution_from_row 0 4 4 12 0 row_00_04_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_12

theorem row_00_04_04_13 : b4RowContribution (![0, 4, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 521 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 21^2 = 521
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_13

theorem weighted_00_04_04_13 : b4RawGapContribution ![0, 4, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 13] = b4GapPatternWeight 4 4 13 * 0 :=
      b4GapContribution_from_row 0 4 4 13 0 row_00_04_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_13

def layers_00_04_04_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 39, 42, 44, 45, 45, 45, 45, 45, 45, 45]]
#print axioms Paper7MomentGapNumeric.layers_00_04_04_14

theorem cells_00_04_04_14 : QTableValid (![0, 4, 8, 22] : Fin 4 → ℕ) layers_00_04_04_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_04_14

theorem valid_00_04_04_14 :
    SparseRowValid (![0, 4, 8, 22] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_04_04_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 8, 22] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 8 + 22 = 34
      decide
    have hzsq : (∑ i, (((![0, 4, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 564 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 8^2 + 22^2 = 564
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_04_14
#print axioms Paper7MomentGapNumeric.valid_00_04_04_14

def qvalues_00_04_04_14 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_04_14

theorem row_00_04_04_14 : b4RowContribution (![0, 4, 8, 22] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![0, 4, 8, 22] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_00_04_04_14) :=
      sparseRow_sound (![0, 4, 8, 22] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_04_04_14) valid_00_04_04_14
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_04_14 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_04_14

theorem weighted_00_04_04_14 : b4RawGapContribution ![0, 4, 4, 14] = 240 := by
  calc
    b4RawGapContribution ![0, 4, 4, 14] = b4GapPatternWeight 4 4 14 * 10 :=
      b4GapContribution_from_row 0 4 4 14 10 row_00_04_04_14
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_14

theorem row_00_04_04_15 : b4RowContribution (![0, 4, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 609 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 23^2 = 609
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_15

theorem weighted_00_04_04_15 : b4RawGapContribution ![0, 4, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 15] = b4GapPatternWeight 4 4 15 * 0 :=
      b4GapContribution_from_row 0 4 4 15 0 row_00_04_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_15

theorem row_00_04_04_16 : b4RowContribution (![0, 4, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 656 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 24^2 = 656
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_16

theorem weighted_00_04_04_16 : b4RawGapContribution ![0, 4, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 16] = b4GapPatternWeight 4 4 16 * 0 :=
      b4GapContribution_from_row 0 4 4 16 0 row_00_04_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_16

theorem row_00_04_04_17 : b4RowContribution (![0, 4, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 8, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 8 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 705 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 8^2 + 25^2 = 705
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_04_17

theorem weighted_00_04_04_17 : b4RawGapContribution ![0, 4, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 4, 17] = b4GapPatternWeight 4 4 17 * 0 :=
      b4GapContribution_from_row 0 4 4 17 0 row_00_04_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_04_17

def dvalues_00_04_04 : Fin 18 → ℕ := ![0, 0, 0, 0, 840, 0, 936, 0, 0, 0, 0, 0, 0, 0, 240, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_04

theorem dblock_00_04_04 : b4GapPatternDBlock 0 4 4 = 2016 := by
  calc
    b4GapPatternDBlock 0 4 4 = ∑ d : Fin 18, dvalues_00_04_04 d := by
      apply b4GapDBlock_of_rows 0 4 4 dvalues_00_04_04
      intro d
      fin_cases d
      · exact weighted_00_04_04_00
      · exact weighted_00_04_04_01
      · exact weighted_00_04_04_02
      · exact weighted_00_04_04_03
      · exact weighted_00_04_04_04
      · exact weighted_00_04_04_05
      · exact weighted_00_04_04_06
      · exact weighted_00_04_04_07
      · exact weighted_00_04_04_08
      · exact weighted_00_04_04_09
      · exact weighted_00_04_04_10
      · exact weighted_00_04_04_11
      · exact weighted_00_04_04_12
      · exact weighted_00_04_04_13
      · exact weighted_00_04_04_14
      · exact weighted_00_04_04_15
      · exact weighted_00_04_04_16
      · exact weighted_00_04_04_17
    _ = 2016 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_04

end Paper7MomentGapNumeric
