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

theorem row_01_01_04_00 : b4RowContribution (![1, 2, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 6 = 15
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 77 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 6^2 = 77
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_00

theorem weighted_01_01_04_00 : b4RawGapContribution ![1, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 1 1 4 0 0 row_01_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_00

theorem row_01_01_04_01 : b4RowContribution (![1, 2, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 7 = 16
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 90 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 7^2 = 90
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_01

theorem weighted_01_01_04_01 : b4RawGapContribution ![1, 1, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 0 :=
      b4GapContribution_from_row 1 1 4 1 0 row_01_01_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_01

theorem row_01_01_04_02 : b4RowContribution (![1, 2, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 8 = 17
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 105 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 8^2 = 105
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_02

theorem weighted_01_01_04_02 : b4RawGapContribution ![1, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 1 1 4 2 0 row_01_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_02

theorem row_01_01_04_03 : b4RowContribution (![1, 2, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 9 = 18
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 9^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_03

theorem weighted_01_01_04_03 : b4RawGapContribution ![1, 1, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 3] = b4GapPatternWeight 1 4 3 * 0 :=
      b4GapContribution_from_row 1 1 4 3 0 row_01_01_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_03

theorem row_01_01_04_04 : b4RowContribution (![1, 2, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 10 = 19
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 141 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 10^2 = 141
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_04

theorem weighted_01_01_04_04 : b4RawGapContribution ![1, 1, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 4] = b4GapPatternWeight 1 4 4 * 0 :=
      b4GapContribution_from_row 1 1 4 4 0 row_01_01_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_04

def layers_01_01_04_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 38, 41, 42, 42, 42, 41, 38, 33, 27, 21, 15, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_01_04_05

theorem cells_01_01_04_05 : QTableValid (![1, 2, 6, 11] : Fin 4 → ℕ) layers_01_01_04_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_04_05

theorem valid_01_01_04_05 :
    SparseRowValid (![1, 2, 6, 11] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_04_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 6, 11] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 6 + 11 = 20
      decide
    have hzsq : (∑ i, (((![1, 2, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 6^2 + 11^2 = 162
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_04_05
#print axioms Paper7MomentGapNumeric.valid_01_01_04_05

def qvalues_01_01_04_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_04_05

theorem row_01_01_04_05 : b4RowContribution (![1, 2, 6, 11] : Fin 4 → ℕ) = 27 := by
  calc
    b4RowContribution (![1, 2, 6, 11] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_01_01_04_05) :=
      sparseRow_sound (![1, 2, 6, 11] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_04_05) valid_01_01_04_05
    _ = 27 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_04_05 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 27 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_04_05

theorem weighted_01_01_04_05 : b4RawGapContribution ![1, 1, 4, 5] = 648 := by
  calc
    b4RawGapContribution ![1, 1, 4, 5] = b4GapPatternWeight 1 4 5 * 27 :=
      b4GapContribution_from_row 1 1 4 5 27 row_01_01_04_05
    _ = 648 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_05

theorem row_01_01_04_06 : b4RowContribution (![1, 2, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 12 = 21
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 12^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_06

theorem weighted_01_01_04_06 : b4RawGapContribution ![1, 1, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 6] = b4GapPatternWeight 1 4 6 * 0 :=
      b4GapContribution_from_row 1 1 4 6 0 row_01_01_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_06

theorem row_01_01_04_07 : b4RowContribution (![1, 2, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 13 = 22
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 13^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_07

theorem weighted_01_01_04_07 : b4RawGapContribution ![1, 1, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 7] = b4GapPatternWeight 1 4 7 * 0 :=
      b4GapContribution_from_row 1 1 4 7 0 row_01_01_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_07

def layers_01_01_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 38, 41, 42, 42, 42, 42, 42, 42, 41, 38, 33, 27]]
#print axioms Paper7MomentGapNumeric.layers_01_01_04_08

theorem cells_01_01_04_08 : QTableValid (![1, 2, 6, 14] : Fin 4 → ℕ) layers_01_01_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_04_08

theorem valid_01_01_04_08 :
    SparseRowValid (![1, 2, 6, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_01_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 6, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 6 + 14 = 23
      decide
    have hzsq : (∑ i, (((![1, 2, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 6^2 + 14^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_04_08
#print axioms Paper7MomentGapNumeric.valid_01_01_04_08

def qvalues_01_01_04_08 : Fin 19 → ℕ := ![0, 0, 0, 15, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_04_08

theorem row_01_01_04_08 : b4RowContribution (![1, 2, 6, 14] : Fin 4 → ℕ) = 57 := by
  calc
    b4RowContribution (![1, 2, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_01_04_08) :=
      sparseRow_sound (![1, 2, 6, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_01_04_08) valid_01_01_04_08
    _ = 57 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_04_08 Q := by
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
        _ = 57 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_04_08

theorem weighted_01_01_04_08 : b4RawGapContribution ![1, 1, 4, 8] = 1368 := by
  calc
    b4RawGapContribution ![1, 1, 4, 8] = b4GapPatternWeight 1 4 8 * 57 :=
      b4GapContribution_from_row 1 1 4 8 57 row_01_01_04_08
    _ = 1368 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_08

theorem row_01_01_04_09 : b4RowContribution (![1, 2, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 15 = 24
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 15^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_09

theorem weighted_01_01_04_09 : b4RawGapContribution ![1, 1, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 9] = b4GapPatternWeight 1 4 9 * 0 :=
      b4GapContribution_from_row 1 1 4 9 0 row_01_01_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_09

theorem row_01_01_04_10 : b4RowContribution (![1, 2, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 16] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 16 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 16^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_10

theorem weighted_01_01_04_10 : b4RawGapContribution ![1, 1, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 10] = b4GapPatternWeight 1 4 10 * 0 :=
      b4GapContribution_from_row 1 1 4 10 0 row_01_01_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_10

theorem row_01_01_04_11 : b4RowContribution (![1, 2, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 17 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 17^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_11

theorem weighted_01_01_04_11 : b4RawGapContribution ![1, 1, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 11] = b4GapPatternWeight 1 4 11 * 0 :=
      b4GapContribution_from_row 1 1 4 11 0 row_01_01_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_11

theorem row_01_01_04_12 : b4RowContribution (![1, 2, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 18 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 18^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_12

theorem weighted_01_01_04_12 : b4RawGapContribution ![1, 1, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 12] = b4GapPatternWeight 1 4 12 * 0 :=
      b4GapContribution_from_row 1 1 4 12 0 row_01_01_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_12

theorem row_01_01_04_13 : b4RowContribution (![1, 2, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 19 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 19^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_13

theorem weighted_01_01_04_13 : b4RawGapContribution ![1, 1, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 13] = b4GapPatternWeight 1 4 13 * 0 :=
      b4GapContribution_from_row 1 1 4 13 0 row_01_01_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_13

theorem row_01_01_04_14 : b4RowContribution (![1, 2, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 20 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 20^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_14

theorem weighted_01_01_04_14 : b4RawGapContribution ![1, 1, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 14] = b4GapPatternWeight 1 4 14 * 0 :=
      b4GapContribution_from_row 1 1 4 14 0 row_01_01_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_14

theorem row_01_01_04_15 : b4RowContribution (![1, 2, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 21 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 21^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_15

theorem weighted_01_01_04_15 : b4RawGapContribution ![1, 1, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 15] = b4GapPatternWeight 1 4 15 * 0 :=
      b4GapContribution_from_row 1 1 4 15 0 row_01_01_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_15

theorem row_01_01_04_16 : b4RowContribution (![1, 2, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 22 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 22^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_16

theorem weighted_01_01_04_16 : b4RawGapContribution ![1, 1, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 16] = b4GapPatternWeight 1 4 16 * 0 :=
      b4GapContribution_from_row 1 1 4 16 0 row_01_01_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_16

def layers_01_01_04_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 38, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42]]
#print axioms Paper7MomentGapNumeric.layers_01_01_04_17

theorem cells_01_01_04_17 : QTableValid (![1, 2, 6, 23] : Fin 4 → ℕ) layers_01_01_04_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_04_17

theorem valid_01_01_04_17 :
    SparseRowValid (![1, 2, 6, 23] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_01_04_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 6, 23] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 6 + 23 = 32
      decide
    have hzsq : (∑ i, (((![1, 2, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 6^2 + 23^2 = 570
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_04_17
#print axioms Paper7MomentGapNumeric.valid_01_01_04_17

def qvalues_01_01_04_17 : Fin 19 → ℕ := ![0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_04_17

theorem row_01_01_04_17 : b4RowContribution (![1, 2, 6, 23] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![1, 2, 6, 23] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_01_04_17) :=
      sparseRow_sound (![1, 2, 6, 23] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_01_04_17) valid_01_01_04_17
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_04_17 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_04_17

theorem weighted_01_01_04_17 : b4RawGapContribution ![1, 1, 4, 17] = 360 := by
  calc
    b4RawGapContribution ![1, 1, 4, 17] = b4GapPatternWeight 1 4 17 * 15 :=
      b4GapContribution_from_row 1 1 4 17 15 row_01_01_04_17
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_17

theorem row_01_01_04_18 : b4RowContribution (![1, 2, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 24 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 617 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 24^2 = 617
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_18

theorem weighted_01_01_04_18 : b4RawGapContribution ![1, 1, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 18] = b4GapPatternWeight 1 4 18 * 0 :=
      b4GapContribution_from_row 1 1 4 18 0 row_01_01_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_18

theorem row_01_01_04_19 : b4RowContribution (![1, 2, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 25 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 666 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 25^2 = 666
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_19

theorem weighted_01_01_04_19 : b4RawGapContribution ![1, 1, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 19] = b4GapPatternWeight 1 4 19 * 0 :=
      b4GapContribution_from_row 1 1 4 19 0 row_01_01_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_19

theorem row_01_01_04_20 : b4RowContribution (![1, 2, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 26 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 717 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 26^2 = 717
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_20

theorem weighted_01_01_04_20 : b4RawGapContribution ![1, 1, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 20] = b4GapPatternWeight 1 4 20 * 0 :=
      b4GapContribution_from_row 1 1 4 20 0 row_01_01_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_20

theorem row_01_01_04_21 : b4RowContribution (![1, 2, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 27 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 770 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 27^2 = 770
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_21

theorem weighted_01_01_04_21 : b4RawGapContribution ![1, 1, 4, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 21] = b4GapPatternWeight 1 4 21 * 0 :=
      b4GapContribution_from_row 1 1 4 21 0 row_01_01_04_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_21

theorem row_01_01_04_22 : b4RowContribution (![1, 2, 6, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 6, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 6 + 28 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 6, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 825 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 6^2 + 28^2 = 825
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_04_22

theorem weighted_01_01_04_22 : b4RawGapContribution ![1, 1, 4, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 4, 22] = b4GapPatternWeight 1 4 22 * 0 :=
      b4GapContribution_from_row 1 1 4 22 0 row_01_01_04_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_04_22

def dvalues_01_01_04 : Fin 23 → ℕ := ![0, 0, 0, 0, 0, 648, 0, 0, 1368, 0, 0, 0, 0, 0, 0, 0, 0, 360, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_04

theorem dblock_01_01_04 : b4GapPatternDBlock 1 1 4 = 2376 := by
  calc
    b4GapPatternDBlock 1 1 4 = ∑ d : Fin 23, dvalues_01_01_04 d := by
      apply b4GapDBlock_of_rows 1 1 4 dvalues_01_01_04
      intro d
      fin_cases d
      · exact weighted_01_01_04_00
      · exact weighted_01_01_04_01
      · exact weighted_01_01_04_02
      · exact weighted_01_01_04_03
      · exact weighted_01_01_04_04
      · exact weighted_01_01_04_05
      · exact weighted_01_01_04_06
      · exact weighted_01_01_04_07
      · exact weighted_01_01_04_08
      · exact weighted_01_01_04_09
      · exact weighted_01_01_04_10
      · exact weighted_01_01_04_11
      · exact weighted_01_01_04_12
      · exact weighted_01_01_04_13
      · exact weighted_01_01_04_14
      · exact weighted_01_01_04_15
      · exact weighted_01_01_04_16
      · exact weighted_01_01_04_17
      · exact weighted_01_01_04_18
      · exact weighted_01_01_04_19
      · exact weighted_01_01_04_20
      · exact weighted_01_01_04_21
      · exact weighted_01_01_04_22
    _ = 2376 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_04

end Paper7MomentGapNumeric
