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

theorem row_02_06_00_00 : b4RowContribution (![2, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 8 = 26
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_00

theorem weighted_02_06_00_00 : b4RawGapContribution ![2, 6, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 0] = b4GapPatternWeight 6 0 0 * 0 :=
      b4GapContribution_from_row 2 6 0 0 0 row_02_06_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_00

theorem row_02_06_00_01 : b4RowContribution (![2, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 9 = 27
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 213
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_01

theorem weighted_02_06_00_01 : b4RawGapContribution ![2, 6, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 1] = b4GapPatternWeight 6 0 1 * 0 :=
      b4GapContribution_from_row 2 6 0 1 0 row_02_06_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_01

def layers_02_06_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 25, 24, 21, 18, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 134, 158, 178, 193, 202, 205, 202, 193, 178, 158]]
#print axioms Paper7MomentGapNumeric.layers_02_06_00_02

theorem cells_02_06_00_02 : QTableValid (![2, 8, 8, 10] : Fin 4 → ℕ) layers_02_06_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_06_00_02

theorem valid_02_06_00_02 :
    SparseRowValid (![2, 8, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_06_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 8, 8, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 8 + 8 + 10 = 28
      decide
    have hzsq : (∑ i, (((![2, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 232 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 232
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06_00_02
#print axioms Paper7MomentGapNumeric.valid_02_06_00_02

def qvalues_02_06_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_06_00_02

theorem row_02_06_00_02 : b4RowContribution (![2, 8, 8, 10] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 8, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_06_00_02) :=
      sparseRow_sound (![2, 8, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_06_00_02) valid_02_06_00_02
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06_00_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_06_00_02

theorem weighted_02_06_00_02 : b4RawGapContribution ![2, 6, 0, 2] = 372 := by
  calc
    b4RawGapContribution ![2, 6, 0, 2] = b4GapPatternWeight 6 0 2 * 31 :=
      b4GapContribution_from_row 2 6 0 2 31 row_02_06_00_02
    _ = 372 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_02

theorem row_02_06_00_03 : b4RowContribution (![2, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 11 = 29
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_03

theorem weighted_02_06_00_03 : b4RawGapContribution ![2, 6, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 3] = b4GapPatternWeight 6 0 3 * 0 :=
      b4GapContribution_from_row 2 6 0 3 0 row_02_06_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_03

def layers_02_06_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 25, 24, 21, 18, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 134, 158, 179, 197, 211, 220, 223, 220, 211, 197]]
#print axioms Paper7MomentGapNumeric.layers_02_06_00_04

theorem cells_02_06_00_04 : QTableValid (![2, 8, 8, 12] : Fin 4 → ℕ) layers_02_06_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_06_00_04

theorem valid_02_06_00_04 :
    SparseRowValid (![2, 8, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_06_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 8, 8, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 8 + 8 + 12 = 30
      decide
    have hzsq : (∑ i, (((![2, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06_00_04
#print axioms Paper7MomentGapNumeric.valid_02_06_00_04

def qvalues_02_06_00_04 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_06_00_04

theorem row_02_06_00_04 : b4RowContribution (![2, 8, 8, 12] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![2, 8, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_06_00_04) :=
      sparseRow_sound (![2, 8, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_06_00_04) valid_02_06_00_04
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06_00_04 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_06_00_04

theorem weighted_02_06_00_04 : b4RawGapContribution ![2, 6, 0, 4] = 228 := by
  calc
    b4RawGapContribution ![2, 6, 0, 4] = b4GapPatternWeight 6 0 4 * 19 :=
      b4GapContribution_from_row 2 6 0 4 19 row_02_06_00_04
    _ = 228 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_04

theorem row_02_06_00_05 : b4RowContribution (![2, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 13 = 31
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_05

theorem weighted_02_06_00_05 : b4RawGapContribution ![2, 6, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 5] = b4GapPatternWeight 6 0 5 * 0 :=
      b4GapContribution_from_row 2 6 0 5 0 row_02_06_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_05

theorem row_02_06_00_06 : b4RowContribution (![2, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 14 = 32
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_06

theorem weighted_02_06_00_06 : b4RawGapContribution ![2, 6, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 6] = b4GapPatternWeight 6 0 6 * 0 :=
      b4GapContribution_from_row 2 6 0 6 0 row_02_06_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_06

theorem row_02_06_00_07 : b4RowContribution (![2, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 15 = 33
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_07

theorem weighted_02_06_00_07 : b4RawGapContribution ![2, 6, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 7] = b4GapPatternWeight 6 0 7 * 0 :=
      b4GapContribution_from_row 2 6 0 7 0 row_02_06_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_07

theorem row_02_06_00_08 : b4RowContribution (![2, 8, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 16 = 34
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 16^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_08

theorem weighted_02_06_00_08 : b4RawGapContribution ![2, 6, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 8] = b4GapPatternWeight 6 0 8 * 0 :=
      b4GapContribution_from_row 2 6 0 8 0 row_02_06_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_08

theorem row_02_06_00_09 : b4RowContribution (![2, 8, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 17 = 35
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 17^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_09

theorem weighted_02_06_00_09 : b4RawGapContribution ![2, 6, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 9] = b4GapPatternWeight 6 0 9 * 0 :=
      b4GapContribution_from_row 2 6 0 9 0 row_02_06_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_09

theorem row_02_06_00_10 : b4RowContribution (![2, 8, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 18 = 36
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 456 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 18^2 = 456
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_10

theorem weighted_02_06_00_10 : b4RawGapContribution ![2, 6, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 10] = b4GapPatternWeight 6 0 10 * 0 :=
      b4GapContribution_from_row 2 6 0 10 0 row_02_06_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_10

theorem row_02_06_00_11 : b4RowContribution (![2, 8, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 8, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 8 + 19 = 37
    decide
  have hzsq : (∑ i, (((![2, 8, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 8^2 + 19^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_00_11

theorem weighted_02_06_00_11 : b4RawGapContribution ![2, 6, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 0, 11] = b4GapPatternWeight 6 0 11 * 0 :=
      b4GapContribution_from_row 2 6 0 11 0 row_02_06_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_00_11

def dvalues_02_06_00 : Fin 12 → ℕ := ![0, 0, 372, 0, 228, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_06_00

theorem dblock_02_06_00 : b4GapPatternDBlock 2 6 0 = 600 := by
  calc
    b4GapPatternDBlock 2 6 0 = ∑ d : Fin 12, dvalues_02_06_00 d := by
      apply b4GapDBlock_of_rows 2 6 0 dvalues_02_06_00
      intro d
      fin_cases d
      · exact weighted_02_06_00_00
      · exact weighted_02_06_00_01
      · exact weighted_02_06_00_02
      · exact weighted_02_06_00_03
      · exact weighted_02_06_00_04
      · exact weighted_02_06_00_05
      · exact weighted_02_06_00_06
      · exact weighted_02_06_00_07
      · exact weighted_02_06_00_08
      · exact weighted_02_06_00_09
      · exact weighted_02_06_00_10
      · exact weighted_02_06_00_11
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_06_00

end Paper7MomentGapNumeric
