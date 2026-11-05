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

theorem row_03_01_04_00 : b4RowContribution (![3, 4, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 8 = 23
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 8^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_00

theorem weighted_03_01_04_00 : b4RawGapContribution ![3, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 3 1 4 0 0 row_03_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_00

theorem row_03_01_04_01 : b4RowContribution (![3, 4, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 9 = 24
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 9^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_01

theorem weighted_03_01_04_01 : b4RawGapContribution ![3, 1, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 0 :=
      b4GapContribution_from_row 3 1 4 1 0 row_03_01_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_01

theorem row_03_01_04_02 : b4RowContribution (![3, 4, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 10 = 25
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 10^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_02

theorem weighted_03_01_04_02 : b4RawGapContribution ![3, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 3 1 4 2 0 row_03_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_02

theorem row_03_01_04_03 : b4RowContribution (![3, 4, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 11 = 26
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 11^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_03

theorem weighted_03_01_04_03 : b4RawGapContribution ![3, 1, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 3] = b4GapPatternWeight 1 4 3 * 0 :=
      b4GapContribution_from_row 3 1 4 3 0 row_03_01_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_03

def layers_03_01_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 129, 146, 160, 170, 175, 175, 170, 160, 146, 129]]
#print axioms Paper7MomentGapNumeric.layers_03_01_04_04

theorem cells_03_01_04_04 : QTableValid (![3, 4, 8, 12] : Fin 4 → ℕ) layers_03_01_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_04_04

theorem valid_03_01_04_04 :
    SparseRowValid (![3, 4, 8, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_01_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 8, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 8 + 12 = 27
      decide
    have hzsq : (∑ i, (((![3, 4, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 8^2 + 12^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_04_04
#print axioms Paper7MomentGapNumeric.valid_03_01_04_04

def qvalues_03_01_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_04_04

theorem row_03_01_04_04 : b4RowContribution (![3, 4, 8, 12] : Fin 4 → ℕ) = 51 := by
  calc
    b4RowContribution (![3, 4, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_01_04_04) :=
      sparseRow_sound (![3, 4, 8, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_01_04_04) valid_03_01_04_04
    _ = 51 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_04_04 Q := by
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
        _ = 51 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_04_04

theorem weighted_03_01_04_04 : b4RawGapContribution ![3, 1, 4, 4] = 1224 := by
  calc
    b4RawGapContribution ![3, 1, 4, 4] = b4GapPatternWeight 1 4 4 * 51 :=
      b4GapContribution_from_row 3 1 4 4 51 row_03_01_04_04
    _ = 1224 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_04

theorem row_03_01_04_05 : b4RowContribution (![3, 4, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 13 = 28
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 13^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_05

theorem weighted_03_01_04_05 : b4RawGapContribution ![3, 1, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 5] = b4GapPatternWeight 1 4 5 * 0 :=
      b4GapContribution_from_row 3 1 4 5 0 row_03_01_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_05

def layers_03_01_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 129, 146, 160, 170, 176, 179, 179, 176, 170, 160]]
#print axioms Paper7MomentGapNumeric.layers_03_01_04_06

theorem cells_03_01_04_06 : QTableValid (![3, 4, 8, 14] : Fin 4 → ℕ) layers_03_01_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_04_06

theorem valid_03_01_04_06 :
    SparseRowValid (![3, 4, 8, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_01_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 8, 14] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 8 + 14 = 29
      decide
    have hzsq : (∑ i, (((![3, 4, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 8^2 + 14^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_04_06
#print axioms Paper7MomentGapNumeric.valid_03_01_04_06

def qvalues_03_01_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_04_06

theorem row_03_01_04_06 : b4RowContribution (![3, 4, 8, 14] : Fin 4 → ℕ) = 70 := by
  calc
    b4RowContribution (![3, 4, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_03_01_04_06) :=
      sparseRow_sound (![3, 4, 8, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_01_04_06) valid_03_01_04_06
    _ = 70 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_04_06 Q := by
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
        _ = 70 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_04_06

theorem weighted_03_01_04_06 : b4RawGapContribution ![3, 1, 4, 6] = 1680 := by
  calc
    b4RawGapContribution ![3, 1, 4, 6] = b4GapPatternWeight 1 4 6 * 70 :=
      b4GapContribution_from_row 3 1 4 6 70 row_03_01_04_06
    _ = 1680 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_06

theorem row_03_01_04_07 : b4RowContribution (![3, 4, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 15 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 15^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_07

theorem weighted_03_01_04_07 : b4RawGapContribution ![3, 1, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 7] = b4GapPatternWeight 1 4 7 * 0 :=
      b4GapContribution_from_row 3 1 4 7 0 row_03_01_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_07

theorem row_03_01_04_08 : b4RowContribution (![3, 4, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 16 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 16^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_08

theorem weighted_03_01_04_08 : b4RawGapContribution ![3, 1, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 8] = b4GapPatternWeight 1 4 8 * 0 :=
      b4GapContribution_from_row 3 1 4 8 0 row_03_01_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_08

theorem row_03_01_04_09 : b4RowContribution (![3, 4, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 17 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 17^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_09

theorem weighted_03_01_04_09 : b4RawGapContribution ![3, 1, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 9] = b4GapPatternWeight 1 4 9 * 0 :=
      b4GapContribution_from_row 3 1 4 9 0 row_03_01_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_09

theorem row_03_01_04_10 : b4RowContribution (![3, 4, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 18 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 18^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_10

theorem weighted_03_01_04_10 : b4RawGapContribution ![3, 1, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 10] = b4GapPatternWeight 1 4 10 * 0 :=
      b4GapContribution_from_row 3 1 4 10 0 row_03_01_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_10

theorem row_03_01_04_11 : b4RowContribution (![3, 4, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 19 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 19^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_11

theorem weighted_03_01_04_11 : b4RawGapContribution ![3, 1, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 11] = b4GapPatternWeight 1 4 11 * 0 :=
      b4GapContribution_from_row 3 1 4 11 0 row_03_01_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_11

theorem row_03_01_04_12 : b4RowContribution (![3, 4, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 20 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 20^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_12

theorem weighted_03_01_04_12 : b4RawGapContribution ![3, 1, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 12] = b4GapPatternWeight 1 4 12 * 0 :=
      b4GapContribution_from_row 3 1 4 12 0 row_03_01_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_12

theorem row_03_01_04_13 : b4RowContribution (![3, 4, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 21 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 21^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_13

theorem weighted_03_01_04_13 : b4RawGapContribution ![3, 1, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 13] = b4GapPatternWeight 1 4 13 * 0 :=
      b4GapContribution_from_row 3 1 4 13 0 row_03_01_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_13

theorem row_03_01_04_14 : b4RowContribution (![3, 4, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 8, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 8 + 22 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 8^2 + 22^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_04_14

theorem weighted_03_01_04_14 : b4RawGapContribution ![3, 1, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 4, 14] = b4GapPatternWeight 1 4 14 * 0 :=
      b4GapContribution_from_row 3 1 4 14 0 row_03_01_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_04_14

def dvalues_03_01_04 : Fin 15 → ℕ := ![0, 0, 0, 0, 1224, 0, 1680, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_04

theorem dblock_03_01_04 : b4GapPatternDBlock 3 1 4 = 2904 := by
  calc
    b4GapPatternDBlock 3 1 4 = ∑ d : Fin 15, dvalues_03_01_04 d := by
      apply b4GapDBlock_of_rows 3 1 4 dvalues_03_01_04
      intro d
      fin_cases d
      · exact weighted_03_01_04_00
      · exact weighted_03_01_04_01
      · exact weighted_03_01_04_02
      · exact weighted_03_01_04_03
      · exact weighted_03_01_04_04
      · exact weighted_03_01_04_05
      · exact weighted_03_01_04_06
      · exact weighted_03_01_04_07
      · exact weighted_03_01_04_08
      · exact weighted_03_01_04_09
      · exact weighted_03_01_04_10
      · exact weighted_03_01_04_11
      · exact weighted_03_01_04_12
      · exact weighted_03_01_04_13
      · exact weighted_03_01_04_14
    _ = 2904 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_04

end Paper7MomentGapNumeric
