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

theorem row_05_01_01_00 : b4RowContribution (![5, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 7] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 7 = 25
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 159 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 159
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_00

theorem weighted_05_01_01_00 : b4RawGapContribution ![5, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 5 1 1 0 0 row_05_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_00

theorem row_05_01_01_01 : b4RowContribution (![5, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 8 = 26
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 174
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_01

theorem weighted_05_01_01_01 : b4RawGapContribution ![5, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 5 1 1 1 0 row_05_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_01

theorem row_05_01_01_02 : b4RowContribution (![5, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 9 = 27
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 191 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 191
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_02

theorem weighted_05_01_01_02 : b4RawGapContribution ![5, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 5 1 1 2 0 row_05_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_02

theorem row_05_01_01_03 : b4RowContribution (![5, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 10 = 28
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_03

theorem weighted_05_01_01_03 : b4RawGapContribution ![5, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 5 1 1 3 0 row_05_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_03

def layers_05_01_01_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 32, 35, 36, 35, 32, 27, 21, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 56, 83, 115, 150, 186, 221, 253, 279, 297, 306, 306, 297, 279, 253]]
#print axioms Paper7MomentGapNumeric.layers_05_01_01_04

theorem cells_05_01_01_04 : QTableValid (![5, 6, 7, 11] : Fin 4 → ℕ) layers_05_01_01_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_01_01_04

theorem valid_05_01_01_04 :
    SparseRowValid (![5, 6, 7, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_01_01_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 6, 7, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 5 + 6 + 7 + 11 = 29
      decide
    have hzsq : (∑ i, (((![5, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_01_01_04
#print axioms Paper7MomentGapNumeric.valid_05_01_01_04

def qvalues_05_01_01_04 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_01_01_04

theorem row_05_01_01_04 : b4RowContribution (![5, 6, 7, 11] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![5, 6, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_05_01_01_04) :=
      sparseRow_sound (![5, 6, 7, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_01_01_04) valid_05_01_01_04
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_01_01_04 Q := by
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
#print axioms Paper7MomentGapNumeric.row_05_01_01_04

theorem weighted_05_01_01_04 : b4RawGapContribution ![5, 1, 1, 4] = 480 := by
  calc
    b4RawGapContribution ![5, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 20 :=
      b4GapContribution_from_row 5 1 1 4 20 row_05_01_01_04
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_04

theorem row_05_01_01_05 : b4RowContribution (![5, 6, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 12 = 30
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_05

theorem weighted_05_01_01_05 : b4RawGapContribution ![5, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 5 1 1 5 0 row_05_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_05

def layers_05_01_01_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 32, 35, 36, 35, 32, 27, 21, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 56, 83, 115, 150, 186, 221, 253, 280, 301, 315, 322, 322, 315, 301]]
#print axioms Paper7MomentGapNumeric.layers_05_01_01_06

theorem cells_05_01_01_06 : QTableValid (![5, 6, 7, 13] : Fin 4 → ℕ) layers_05_01_01_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_01_01_06

theorem valid_05_01_01_06 :
    SparseRowValid (![5, 6, 7, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_01_01_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 6, 7, 13] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 5 + 6 + 7 + 13 = 31
      decide
    have hzsq : (∑ i, (((![5, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_01_01_06
#print axioms Paper7MomentGapNumeric.valid_05_01_01_06

def qvalues_05_01_01_06 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_01_01_06

theorem row_05_01_01_06 : b4RowContribution (![5, 6, 7, 13] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![5, 6, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_01_01_06) :=
      sparseRow_sound (![5, 6, 7, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_01_01_06) valid_05_01_01_06
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_01_01_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_05_01_01_06

theorem weighted_05_01_01_06 : b4RawGapContribution ![5, 1, 1, 6] = 2016 := by
  calc
    b4RawGapContribution ![5, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 84 :=
      b4GapContribution_from_row 5 1 1 6 84 row_05_01_01_06
    _ = 2016 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_06

theorem row_05_01_01_07 : b4RowContribution (![5, 6, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 14 = 32
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_07

theorem weighted_05_01_01_07 : b4RawGapContribution ![5, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 5 1 1 7 0 row_05_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_07

theorem row_05_01_01_08 : b4RowContribution (![5, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 15 = 33
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_08

theorem weighted_05_01_01_08 : b4RawGapContribution ![5, 1, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 0 :=
      b4GapContribution_from_row 5 1 1 8 0 row_05_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_08

theorem row_05_01_01_09 : b4RowContribution (![5, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 16 = 34
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_09

theorem weighted_05_01_01_09 : b4RawGapContribution ![5, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 5 1 1 9 0 row_05_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_09

theorem row_05_01_01_10 : b4RowContribution (![5, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 17 = 35
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_10

theorem weighted_05_01_01_10 : b4RawGapContribution ![5, 1, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 0 :=
      b4GapContribution_from_row 5 1 1 10 0 row_05_01_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_10

theorem row_05_01_01_11 : b4RowContribution (![5, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 18 = 36
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_11

theorem weighted_05_01_01_11 : b4RawGapContribution ![5, 1, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 0 :=
      b4GapContribution_from_row 5 1 1 11 0 row_05_01_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_11

theorem row_05_01_01_12 : b4RowContribution (![5, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 7, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 7 + 19 = 37
    decide
  have hzsq : (∑ i, (((![5, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_01_12

theorem weighted_05_01_01_12 : b4RawGapContribution ![5, 1, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 0 :=
      b4GapContribution_from_row 5 1 1 12 0 row_05_01_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_01_12

def dvalues_05_01_01 : Fin 13 → ℕ := ![0, 0, 0, 0, 480, 0, 2016, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_01_01

theorem dblock_05_01_01 : b4GapPatternDBlock 5 1 1 = 2496 := by
  calc
    b4GapPatternDBlock 5 1 1 = ∑ d : Fin 13, dvalues_05_01_01 d := by
      apply b4GapDBlock_of_rows 5 1 1 dvalues_05_01_01
      intro d
      fin_cases d
      · exact weighted_05_01_01_00
      · exact weighted_05_01_01_01
      · exact weighted_05_01_01_02
      · exact weighted_05_01_01_03
      · exact weighted_05_01_01_04
      · exact weighted_05_01_01_05
      · exact weighted_05_01_01_06
      · exact weighted_05_01_01_07
      · exact weighted_05_01_01_08
      · exact weighted_05_01_01_09
      · exact weighted_05_01_01_10
      · exact weighted_05_01_01_11
      · exact weighted_05_01_01_12
    _ = 2496 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_01_01

end Paper7MomentGapNumeric
