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

theorem row_02_00_05_00 : b4RowContribution (![2, 2, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 7 = 18
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 106 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 7^2 = 106
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_00

theorem weighted_02_00_05_00 : b4RawGapContribution ![2, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 2 0 5 0 0 row_02_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_00

theorem row_02_00_05_01 : b4RowContribution (![2, 2, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 8 = 19
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 121 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 8^2 = 121
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_01

theorem weighted_02_00_05_01 : b4RawGapContribution ![2, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 2 0 5 1 0 row_02_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_01

theorem row_02_00_05_02 : b4RowContribution (![2, 2, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 9 = 20
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 9^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_02

theorem weighted_02_00_05_02 : b4RawGapContribution ![2, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 2 0 5 2 0 row_02_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_02

theorem row_02_00_05_03 : b4RowContribution (![2, 2, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 10 = 21
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 157 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 10^2 = 157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_03

theorem weighted_02_00_05_03 : b4RawGapContribution ![2, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 2 0 5 3 0 row_02_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_03

theorem row_02_00_05_04 : b4RowContribution (![2, 2, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 11 = 22
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 11^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_04

theorem weighted_02_00_05_04 : b4RawGapContribution ![2, 0, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 0 :=
      b4GapContribution_from_row 2 0 5 4 0 row_02_00_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_04

theorem row_02_00_05_05 : b4RowContribution (![2, 2, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 12 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 12^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_05

theorem weighted_02_00_05_05 : b4RawGapContribution ![2, 0, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 0 :=
      b4GapContribution_from_row 2 0 5 5 0 row_02_00_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_05

def layers_02_00_05_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 62, 68, 71, 72, 72, 72, 71, 68, 62, 54, 45]]
#print axioms Paper7MomentGapNumeric.layers_02_00_05_06

theorem cells_02_00_05_06 : QTableValid (![2, 2, 7, 13] : Fin 4 → ℕ) layers_02_00_05_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_05_06

theorem valid_02_00_05_06 :
    SparseRowValid (![2, 2, 7, 13] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_05_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 7, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 7 + 13 = 24
      decide
    have hzsq : (∑ i, (((![2, 2, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 7^2 + 13^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_05_06
#print axioms Paper7MomentGapNumeric.valid_02_00_05_06

def qvalues_02_00_05_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_05_06

theorem row_02_00_05_06 : b4RowContribution (![2, 2, 7, 13] : Fin 4 → ℕ) = 126 := by
  calc
    b4RowContribution (![2, 2, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_05_06) :=
      sparseRow_sound (![2, 2, 7, 13] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_05_06) valid_02_00_05_06
    _ = 126 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_05_06 Q := by
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
        _ = 126 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_05_06

theorem weighted_02_00_05_06 : b4RawGapContribution ![2, 0, 5, 6] = 1512 := by
  calc
    b4RawGapContribution ![2, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 126 :=
      b4GapContribution_from_row 2 0 5 6 126 row_02_00_05_06
    _ = 1512 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_06

theorem row_02_00_05_07 : b4RowContribution (![2, 2, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 14 = 25
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 14^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_07

theorem weighted_02_00_05_07 : b4RawGapContribution ![2, 0, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 0 :=
      b4GapContribution_from_row 2 0 5 7 0 row_02_00_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_07

def layers_02_00_05_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 62, 68, 71, 72, 72, 72, 72, 72, 71, 68, 62]]
#print axioms Paper7MomentGapNumeric.layers_02_00_05_08

theorem cells_02_00_05_08 : QTableValid (![2, 2, 7, 15] : Fin 4 → ℕ) layers_02_00_05_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_05_08

theorem valid_02_00_05_08 :
    SparseRowValid (![2, 2, 7, 15] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_00_05_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 7, 15] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 7 + 15 = 26
      decide
    have hzsq : (∑ i, (((![2, 2, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 7^2 + 15^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_05_08
#print axioms Paper7MomentGapNumeric.valid_02_00_05_08

def qvalues_02_00_05_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_05_08

theorem row_02_00_05_08 : b4RowContribution (![2, 2, 7, 15] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![2, 2, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_00_05_08) :=
      sparseRow_sound (![2, 2, 7, 15] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_00_05_08) valid_02_00_05_08
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_05_08 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_05_08

theorem weighted_02_00_05_08 : b4RawGapContribution ![2, 0, 5, 8] = 540 := by
  calc
    b4RawGapContribution ![2, 0, 5, 8] = b4GapPatternWeight 0 5 8 * 45 :=
      b4GapContribution_from_row 2 0 5 8 45 row_02_00_05_08
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_08

theorem row_02_00_05_09 : b4RowContribution (![2, 2, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 16 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 16^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_09

theorem weighted_02_00_05_09 : b4RawGapContribution ![2, 0, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 9] = b4GapPatternWeight 0 5 9 * 0 :=
      b4GapContribution_from_row 2 0 5 9 0 row_02_00_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_09

theorem row_02_00_05_10 : b4RowContribution (![2, 2, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 17 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 17^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_10

theorem weighted_02_00_05_10 : b4RawGapContribution ![2, 0, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 10] = b4GapPatternWeight 0 5 10 * 0 :=
      b4GapContribution_from_row 2 0 5 10 0 row_02_00_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_10

theorem row_02_00_05_11 : b4RowContribution (![2, 2, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 18 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 18^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_11

theorem weighted_02_00_05_11 : b4RawGapContribution ![2, 0, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 11] = b4GapPatternWeight 0 5 11 * 0 :=
      b4GapContribution_from_row 2 0 5 11 0 row_02_00_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_11

theorem row_02_00_05_12 : b4RowContribution (![2, 2, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 19 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 19^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_12

theorem weighted_02_00_05_12 : b4RawGapContribution ![2, 0, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 12] = b4GapPatternWeight 0 5 12 * 0 :=
      b4GapContribution_from_row 2 0 5 12 0 row_02_00_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_12

theorem row_02_00_05_13 : b4RowContribution (![2, 2, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 20 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 20^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_13

theorem weighted_02_00_05_13 : b4RawGapContribution ![2, 0, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 13] = b4GapPatternWeight 0 5 13 * 0 :=
      b4GapContribution_from_row 2 0 5 13 0 row_02_00_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_13

theorem row_02_00_05_14 : b4RowContribution (![2, 2, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 21 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 21^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_14

theorem weighted_02_00_05_14 : b4RawGapContribution ![2, 0, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 14] = b4GapPatternWeight 0 5 14 * 0 :=
      b4GapContribution_from_row 2 0 5 14 0 row_02_00_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_14

theorem row_02_00_05_15 : b4RowContribution (![2, 2, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 22 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 541 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 22^2 = 541
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_15

theorem weighted_02_00_05_15 : b4RawGapContribution ![2, 0, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 15] = b4GapPatternWeight 0 5 15 * 0 :=
      b4GapContribution_from_row 2 0 5 15 0 row_02_00_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_15

theorem row_02_00_05_16 : b4RowContribution (![2, 2, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 23 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 586 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 23^2 = 586
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_16

theorem weighted_02_00_05_16 : b4RawGapContribution ![2, 0, 5, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 16] = b4GapPatternWeight 0 5 16 * 0 :=
      b4GapContribution_from_row 2 0 5 16 0 row_02_00_05_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_16

theorem row_02_00_05_17 : b4RowContribution (![2, 2, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 24 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 633 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 24^2 = 633
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_17

theorem weighted_02_00_05_17 : b4RawGapContribution ![2, 0, 5, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 17] = b4GapPatternWeight 0 5 17 * 0 :=
      b4GapContribution_from_row 2 0 5 17 0 row_02_00_05_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_17

theorem row_02_00_05_18 : b4RowContribution (![2, 2, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 25 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 682 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 25^2 = 682
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_18

theorem weighted_02_00_05_18 : b4RawGapContribution ![2, 0, 5, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 18] = b4GapPatternWeight 0 5 18 * 0 :=
      b4GapContribution_from_row 2 0 5 18 0 row_02_00_05_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_18

theorem row_02_00_05_19 : b4RowContribution (![2, 2, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 7, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 7 + 26 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 733 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 7^2 + 26^2 = 733
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_05_19

theorem weighted_02_00_05_19 : b4RawGapContribution ![2, 0, 5, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 5, 19] = b4GapPatternWeight 0 5 19 * 0 :=
      b4GapContribution_from_row 2 0 5 19 0 row_02_00_05_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_05_19

def dvalues_02_00_05 : Fin 20 → ℕ := ![0, 0, 0, 0, 0, 0, 1512, 0, 540, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_05

theorem dblock_02_00_05 : b4GapPatternDBlock 2 0 5 = 2052 := by
  calc
    b4GapPatternDBlock 2 0 5 = ∑ d : Fin 20, dvalues_02_00_05 d := by
      apply b4GapDBlock_of_rows 2 0 5 dvalues_02_00_05
      intro d
      fin_cases d
      · exact weighted_02_00_05_00
      · exact weighted_02_00_05_01
      · exact weighted_02_00_05_02
      · exact weighted_02_00_05_03
      · exact weighted_02_00_05_04
      · exact weighted_02_00_05_05
      · exact weighted_02_00_05_06
      · exact weighted_02_00_05_07
      · exact weighted_02_00_05_08
      · exact weighted_02_00_05_09
      · exact weighted_02_00_05_10
      · exact weighted_02_00_05_11
      · exact weighted_02_00_05_12
      · exact weighted_02_00_05_13
      · exact weighted_02_00_05_14
      · exact weighted_02_00_05_15
      · exact weighted_02_00_05_16
      · exact weighted_02_00_05_17
      · exact weighted_02_00_05_18
      · exact weighted_02_00_05_19
    _ = 2052 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_05

end Paper7MomentGapNumeric
