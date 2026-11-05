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

theorem row_02_02_04_00 : b4RowContribution (![2, 4, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 8 = 22
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 8^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_00

theorem weighted_02_02_04_00 : b4RawGapContribution ![2, 2, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 0] = b4GapPatternWeight 2 4 0 * 0 :=
      b4GapContribution_from_row 2 2 4 0 0 row_02_02_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_00

theorem row_02_02_04_01 : b4RowContribution (![2, 4, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 9 = 23
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 9^2 = 165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_01

theorem weighted_02_02_04_01 : b4RawGapContribution ![2, 2, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 1] = b4GapPatternWeight 2 4 1 * 0 :=
      b4GapContribution_from_row 2 2 4 1 0 row_02_02_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_01

theorem row_02_02_04_02 : b4RowContribution (![2, 4, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 10 = 24
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 184 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 10^2 = 184
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_02

theorem weighted_02_02_04_02 : b4RawGapContribution ![2, 2, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 2] = b4GapPatternWeight 2 4 2 * 0 :=
      b4GapContribution_from_row 2 2 4 2 0 row_02_02_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_02

theorem row_02_02_04_03 : b4RowContribution (![2, 4, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 11 = 25
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 11^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_03

theorem weighted_02_02_04_03 : b4RawGapContribution ![2, 2, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 3] = b4GapPatternWeight 2 4 3 * 0 :=
      b4GapContribution_from_row 2 2 4 3 0 row_02_02_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_03

def layers_02_02_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 90, 104, 116, 125, 131, 133, 131, 125, 116, 104, 90]]
#print axioms Paper7MomentGapNumeric.layers_02_02_04_04

theorem cells_02_02_04_04 : QTableValid (![2, 4, 8, 12] : Fin 4 → ℕ) layers_02_02_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_04_04

theorem valid_02_02_04_04 :
    SparseRowValid (![2, 4, 8, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_02_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 8, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 8 + 12 = 26
      decide
    have hzsq : (∑ i, (((![2, 4, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 8^2 + 12^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_04_04
#print axioms Paper7MomentGapNumeric.valid_02_02_04_04

def qvalues_02_02_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_04_04

theorem row_02_02_04_04 : b4RowContribution (![2, 4, 8, 12] : Fin 4 → ℕ) = 104 := by
  calc
    b4RowContribution (![2, 4, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_02_04_04) :=
      sparseRow_sound (![2, 4, 8, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_02_04_04) valid_02_02_04_04
    _ = 104 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_04_04 Q := by
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
        _ = 104 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_04_04

theorem weighted_02_02_04_04 : b4RawGapContribution ![2, 2, 4, 4] = 2496 := by
  calc
    b4RawGapContribution ![2, 2, 4, 4] = b4GapPatternWeight 2 4 4 * 104 :=
      b4GapContribution_from_row 2 2 4 4 104 row_02_02_04_04
    _ = 2496 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_04

theorem row_02_02_04_05 : b4RowContribution (![2, 4, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 13 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 13^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_05

theorem weighted_02_02_04_05 : b4RawGapContribution ![2, 2, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 5] = b4GapPatternWeight 2 4 5 * 0 :=
      b4GapContribution_from_row 2 2 4 5 0 row_02_02_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_05

def layers_02_02_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 90, 104, 116, 125, 131, 134, 135, 134, 131, 125, 116]]
#print axioms Paper7MomentGapNumeric.layers_02_02_04_06

theorem cells_02_02_04_06 : QTableValid (![2, 4, 8, 14] : Fin 4 → ℕ) layers_02_02_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_04_06

theorem valid_02_02_04_06 :
    SparseRowValid (![2, 4, 8, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 8, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 8 + 14 = 28
      decide
    have hzsq : (∑ i, (((![2, 4, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 280 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 8^2 + 14^2 = 280
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_04_06
#print axioms Paper7MomentGapNumeric.valid_02_02_04_06

def qvalues_02_02_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_04_06

theorem row_02_02_04_06 : b4RowContribution (![2, 4, 8, 14] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 4, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_02_04_06) :=
      sparseRow_sound (![2, 4, 8, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_04_06) valid_02_02_04_06
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_04_06 Q := by
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
        _ = 31 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_04_06

theorem weighted_02_02_04_06 : b4RawGapContribution ![2, 2, 4, 6] = 744 := by
  calc
    b4RawGapContribution ![2, 2, 4, 6] = b4GapPatternWeight 2 4 6 * 31 :=
      b4GapContribution_from_row 2 2 4 6 31 row_02_02_04_06
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_06

theorem row_02_02_04_07 : b4RowContribution (![2, 4, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 15 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 15^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_07

theorem weighted_02_02_04_07 : b4RawGapContribution ![2, 2, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 7] = b4GapPatternWeight 2 4 7 * 0 :=
      b4GapContribution_from_row 2 2 4 7 0 row_02_02_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_07

theorem row_02_02_04_08 : b4RowContribution (![2, 4, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 16 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 16^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_08

theorem weighted_02_02_04_08 : b4RawGapContribution ![2, 2, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 8] = b4GapPatternWeight 2 4 8 * 0 :=
      b4GapContribution_from_row 2 2 4 8 0 row_02_02_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_08

theorem row_02_02_04_09 : b4RowContribution (![2, 4, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 17 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 17^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_09

theorem weighted_02_02_04_09 : b4RawGapContribution ![2, 2, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 9] = b4GapPatternWeight 2 4 9 * 0 :=
      b4GapContribution_from_row 2 2 4 9 0 row_02_02_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_09

theorem row_02_02_04_10 : b4RowContribution (![2, 4, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 18 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 408 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 18^2 = 408
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_10

theorem weighted_02_02_04_10 : b4RawGapContribution ![2, 2, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 10] = b4GapPatternWeight 2 4 10 * 0 :=
      b4GapContribution_from_row 2 2 4 10 0 row_02_02_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_10

theorem row_02_02_04_11 : b4RowContribution (![2, 4, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 19 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 19^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_11

theorem weighted_02_02_04_11 : b4RawGapContribution ![2, 2, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 11] = b4GapPatternWeight 2 4 11 * 0 :=
      b4GapContribution_from_row 2 2 4 11 0 row_02_02_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_11

theorem row_02_02_04_12 : b4RowContribution (![2, 4, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 20 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 484 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 20^2 = 484
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_12

theorem weighted_02_02_04_12 : b4RawGapContribution ![2, 2, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 12] = b4GapPatternWeight 2 4 12 * 0 :=
      b4GapContribution_from_row 2 2 4 12 0 row_02_02_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_12

theorem row_02_02_04_13 : b4RowContribution (![2, 4, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 21 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 21^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_13

theorem weighted_02_02_04_13 : b4RawGapContribution ![2, 2, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 13] = b4GapPatternWeight 2 4 13 * 0 :=
      b4GapContribution_from_row 2 2 4 13 0 row_02_02_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_13

theorem row_02_02_04_14 : b4RowContribution (![2, 4, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 22 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 568 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 22^2 = 568
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_14

theorem weighted_02_02_04_14 : b4RawGapContribution ![2, 2, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 14] = b4GapPatternWeight 2 4 14 * 0 :=
      b4GapContribution_from_row 2 2 4 14 0 row_02_02_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_14

theorem row_02_02_04_15 : b4RowContribution (![2, 4, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 8, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 8 + 23 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 613 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 8^2 + 23^2 = 613
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_04_15

theorem weighted_02_02_04_15 : b4RawGapContribution ![2, 2, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 4, 15] = b4GapPatternWeight 2 4 15 * 0 :=
      b4GapContribution_from_row 2 2 4 15 0 row_02_02_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_04_15

def dvalues_02_02_04 : Fin 16 → ℕ := ![0, 0, 0, 0, 2496, 0, 744, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_04

theorem dblock_02_02_04 : b4GapPatternDBlock 2 2 4 = 3240 := by
  calc
    b4GapPatternDBlock 2 2 4 = ∑ d : Fin 16, dvalues_02_02_04 d := by
      apply b4GapDBlock_of_rows 2 2 4 dvalues_02_02_04
      intro d
      fin_cases d
      · exact weighted_02_02_04_00
      · exact weighted_02_02_04_01
      · exact weighted_02_02_04_02
      · exact weighted_02_02_04_03
      · exact weighted_02_02_04_04
      · exact weighted_02_02_04_05
      · exact weighted_02_02_04_06
      · exact weighted_02_02_04_07
      · exact weighted_02_02_04_08
      · exact weighted_02_02_04_09
      · exact weighted_02_02_04_10
      · exact weighted_02_02_04_11
      · exact weighted_02_02_04_12
      · exact weighted_02_02_04_13
      · exact weighted_02_02_04_14
      · exact weighted_02_02_04_15
    _ = 3240 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_04

end Paper7MomentGapNumeric
