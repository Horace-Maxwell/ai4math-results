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

theorem row_01_02_04_00 : b4RowContribution (![1, 3, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 7 = 18
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 7^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_00

theorem weighted_01_02_04_00 : b4RawGapContribution ![1, 2, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 0] = b4GapPatternWeight 2 4 0 * 0 :=
      b4GapContribution_from_row 1 2 4 0 0 row_01_02_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_00

theorem row_01_02_04_01 : b4RowContribution (![1, 3, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 8 = 19
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 8^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_01

theorem weighted_01_02_04_01 : b4RawGapContribution ![1, 2, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 1] = b4GapPatternWeight 2 4 1 * 0 :=
      b4GapContribution_from_row 1 2 4 1 0 row_01_02_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_01

theorem row_01_02_04_02 : b4RowContribution (![1, 3, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 9 = 20
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 140 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 9^2 = 140
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_02

theorem weighted_01_02_04_02 : b4RawGapContribution ![1, 2, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 2] = b4GapPatternWeight 2 4 2 * 0 :=
      b4GapContribution_from_row 1 2 4 2 0 row_01_02_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_02

theorem row_01_02_04_03 : b4RowContribution (![1, 3, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 10 = 21
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 159 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 10^2 = 159
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_03

theorem weighted_01_02_04_03 : b4RawGapContribution ![1, 2, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 3] = b4GapPatternWeight 2 4 3 * 0 :=
      b4GapContribution_from_row 1 2 4 3 0 row_01_02_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_03

theorem row_01_02_04_04 : b4RowContribution (![1, 3, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 11 = 22
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 11^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_04

theorem weighted_01_02_04_04 : b4RawGapContribution ![1, 2, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 4] = b4GapPatternWeight 2 4 4 * 0 :=
      b4GapContribution_from_row 1 2 4 4 0 row_01_02_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_04

theorem row_01_02_04_05 : b4RowContribution (![1, 3, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 12 = 23
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 12^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_05

theorem weighted_01_02_04_05 : b4RawGapContribution ![1, 2, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 5] = b4GapPatternWeight 2 4 5 * 0 :=
      b4GapContribution_from_row 1 2 4 5 0 row_01_02_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_05

def layers_01_02_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 55, 60, 63, 64, 64, 64, 63, 60, 55, 48, 40]]
#print axioms Paper7MomentGapNumeric.layers_01_02_04_06

theorem cells_01_02_04_06 : QTableValid (![1, 3, 7, 13] : Fin 4 → ℕ) layers_01_02_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_04_06

theorem valid_01_02_04_06 :
    SparseRowValid (![1, 3, 7, 13] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 7, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 7 + 13 = 24
      decide
    have hzsq : (∑ i, (((![1, 3, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 7^2 + 13^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_04_06
#print axioms Paper7MomentGapNumeric.valid_01_02_04_06

def qvalues_01_02_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_04_06

theorem row_01_02_04_06 : b4RowContribution (![1, 3, 7, 13] : Fin 4 → ℕ) = 104 := by
  calc
    b4RowContribution (![1, 3, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_04_06) :=
      sparseRow_sound (![1, 3, 7, 13] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_04_06) valid_01_02_04_06
    _ = 104 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_04_06 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 104 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_04_06

theorem weighted_01_02_04_06 : b4RawGapContribution ![1, 2, 4, 6] = 2496 := by
  calc
    b4RawGapContribution ![1, 2, 4, 6] = b4GapPatternWeight 2 4 6 * 104 :=
      b4GapContribution_from_row 1 2 4 6 104 row_01_02_04_06
    _ = 2496 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_06

theorem row_01_02_04_07 : b4RowContribution (![1, 3, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 14 = 25
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 14^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_07

theorem weighted_01_02_04_07 : b4RawGapContribution ![1, 2, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 7] = b4GapPatternWeight 2 4 7 * 0 :=
      b4GapContribution_from_row 1 2 4 7 0 row_01_02_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_07

def layers_01_02_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 55, 60, 63, 64, 64, 64, 64, 64, 63, 60, 55]]
#print axioms Paper7MomentGapNumeric.layers_01_02_04_08

theorem cells_01_02_04_08 : QTableValid (![1, 3, 7, 15] : Fin 4 → ℕ) layers_01_02_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_04_08

theorem valid_01_02_04_08 :
    SparseRowValid (![1, 3, 7, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_02_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 7, 15] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 7 + 15 = 26
      decide
    have hzsq : (∑ i, (((![1, 3, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 7^2 + 15^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_04_08
#print axioms Paper7MomentGapNumeric.valid_01_02_04_08

def qvalues_01_02_04_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_04_08

theorem row_01_02_04_08 : b4RowContribution (![1, 3, 7, 15] : Fin 4 → ℕ) = 96 := by
  calc
    b4RowContribution (![1, 3, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_02_04_08) :=
      sparseRow_sound (![1, 3, 7, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_02_04_08) valid_01_02_04_08
    _ = 96 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_04_08 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_04_08

theorem weighted_01_02_04_08 : b4RawGapContribution ![1, 2, 4, 8] = 2304 := by
  calc
    b4RawGapContribution ![1, 2, 4, 8] = b4GapPatternWeight 2 4 8 * 96 :=
      b4GapContribution_from_row 1 2 4 8 96 row_01_02_04_08
    _ = 2304 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_08

theorem row_01_02_04_09 : b4RowContribution (![1, 3, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 16 = 27
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 16^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_09

theorem weighted_01_02_04_09 : b4RawGapContribution ![1, 2, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 9] = b4GapPatternWeight 2 4 9 * 0 :=
      b4GapContribution_from_row 1 2 4 9 0 row_01_02_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_09

theorem row_01_02_04_10 : b4RowContribution (![1, 3, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 17 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 17^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_10

theorem weighted_01_02_04_10 : b4RawGapContribution ![1, 2, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 10] = b4GapPatternWeight 2 4 10 * 0 :=
      b4GapContribution_from_row 1 2 4 10 0 row_01_02_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_10

theorem row_01_02_04_11 : b4RowContribution (![1, 3, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 18 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 18^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_11

theorem weighted_01_02_04_11 : b4RawGapContribution ![1, 2, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 11] = b4GapPatternWeight 2 4 11 * 0 :=
      b4GapContribution_from_row 1 2 4 11 0 row_01_02_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_11

theorem row_01_02_04_12 : b4RowContribution (![1, 3, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 19 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 19^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_12

theorem weighted_01_02_04_12 : b4RawGapContribution ![1, 2, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 12] = b4GapPatternWeight 2 4 12 * 0 :=
      b4GapContribution_from_row 1 2 4 12 0 row_01_02_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_12

theorem row_01_02_04_13 : b4RowContribution (![1, 3, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 20 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 20^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_13

theorem weighted_01_02_04_13 : b4RawGapContribution ![1, 2, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 13] = b4GapPatternWeight 2 4 13 * 0 :=
      b4GapContribution_from_row 1 2 4 13 0 row_01_02_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_13

theorem row_01_02_04_14 : b4RowContribution (![1, 3, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 21 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 500 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 21^2 = 500
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_14

theorem weighted_01_02_04_14 : b4RawGapContribution ![1, 2, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 14] = b4GapPatternWeight 2 4 14 * 0 :=
      b4GapContribution_from_row 1 2 4 14 0 row_01_02_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_14

theorem row_01_02_04_15 : b4RowContribution (![1, 3, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 22 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 543 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 22^2 = 543
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_15

theorem weighted_01_02_04_15 : b4RawGapContribution ![1, 2, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 15] = b4GapPatternWeight 2 4 15 * 0 :=
      b4GapContribution_from_row 1 2 4 15 0 row_01_02_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_15

theorem row_01_02_04_16 : b4RowContribution (![1, 3, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 23 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 588 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 23^2 = 588
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_16

theorem weighted_01_02_04_16 : b4RawGapContribution ![1, 2, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 16] = b4GapPatternWeight 2 4 16 * 0 :=
      b4GapContribution_from_row 1 2 4 16 0 row_01_02_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_16

theorem row_01_02_04_17 : b4RowContribution (![1, 3, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 24 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 635 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 24^2 = 635
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_17

theorem weighted_01_02_04_17 : b4RawGapContribution ![1, 2, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 17] = b4GapPatternWeight 2 4 17 * 0 :=
      b4GapContribution_from_row 1 2 4 17 0 row_01_02_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_17

theorem row_01_02_04_18 : b4RowContribution (![1, 3, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 25 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 684 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 25^2 = 684
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_18

theorem weighted_01_02_04_18 : b4RawGapContribution ![1, 2, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 18] = b4GapPatternWeight 2 4 18 * 0 :=
      b4GapContribution_from_row 1 2 4 18 0 row_01_02_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_18

theorem row_01_02_04_19 : b4RowContribution (![1, 3, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 7, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 7 + 26 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 735 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 7^2 + 26^2 = 735
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_04_19

theorem weighted_01_02_04_19 : b4RawGapContribution ![1, 2, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 4, 19] = b4GapPatternWeight 2 4 19 * 0 :=
      b4GapContribution_from_row 1 2 4 19 0 row_01_02_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_04_19

def dvalues_01_02_04 : Fin 20 → ℕ := ![0, 0, 0, 0, 0, 0, 2496, 0, 2304, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_04

theorem dblock_01_02_04 : b4GapPatternDBlock 1 2 4 = 4800 := by
  calc
    b4GapPatternDBlock 1 2 4 = ∑ d : Fin 20, dvalues_01_02_04 d := by
      apply b4GapDBlock_of_rows 1 2 4 dvalues_01_02_04
      intro d
      fin_cases d
      · exact weighted_01_02_04_00
      · exact weighted_01_02_04_01
      · exact weighted_01_02_04_02
      · exact weighted_01_02_04_03
      · exact weighted_01_02_04_04
      · exact weighted_01_02_04_05
      · exact weighted_01_02_04_06
      · exact weighted_01_02_04_07
      · exact weighted_01_02_04_08
      · exact weighted_01_02_04_09
      · exact weighted_01_02_04_10
      · exact weighted_01_02_04_11
      · exact weighted_01_02_04_12
      · exact weighted_01_02_04_13
      · exact weighted_01_02_04_14
      · exact weighted_01_02_04_15
      · exact weighted_01_02_04_16
      · exact weighted_01_02_04_17
      · exact weighted_01_02_04_18
      · exact weighted_01_02_04_19
    _ = 4800 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_04

end Paper7MomentGapNumeric
