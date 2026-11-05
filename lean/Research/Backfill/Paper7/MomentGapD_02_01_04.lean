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

theorem row_02_01_04_00 : b4RowContribution (![2, 3, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 7] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 7 = 19
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 111 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 7^2 = 111
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_00

theorem weighted_02_01_04_00 : b4RawGapContribution ![2, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 2 1 4 0 0 row_02_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_00

theorem row_02_01_04_01 : b4RowContribution (![2, 3, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 8 = 20
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 8^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_01

theorem weighted_02_01_04_01 : b4RawGapContribution ![2, 1, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 0 :=
      b4GapContribution_from_row 2 1 4 1 0 row_02_01_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_01

theorem row_02_01_04_02 : b4RowContribution (![2, 3, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 9 = 21
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 143 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 9^2 = 143
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_02

theorem weighted_02_01_04_02 : b4RawGapContribution ![2, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 2 1 4 2 0 row_02_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_02

theorem row_02_01_04_03 : b4RowContribution (![2, 3, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 10 = 22
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 10^2 = 162
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_03

theorem weighted_02_01_04_03 : b4RawGapContribution ![2, 1, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 3] = b4GapPatternWeight 1 4 3 * 0 :=
      b4GapContribution_from_row 2 1 4 3 0 row_02_01_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_03

theorem row_02_01_04_04 : b4RowContribution (![2, 3, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 11 = 23
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 11^2 = 183
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_04

theorem weighted_02_01_04_04 : b4RawGapContribution ![2, 1, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 4] = b4GapPatternWeight 1 4 4 * 0 :=
      b4GapContribution_from_row 2 1 4 4 0 row_02_01_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_04

theorem row_02_01_04_05 : b4RowContribution (![2, 3, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 12 = 24
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 12^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_05

theorem weighted_02_01_04_05 : b4RawGapContribution ![2, 1, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 5] = b4GapPatternWeight 1 4 5 * 0 :=
      b4GapContribution_from_row 2 1 4 5 0 row_02_01_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_05

def layers_02_01_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 77, 86, 92, 95, 96, 96, 95, 92, 86, 77, 66]]
#print axioms Paper7MomentGapNumeric.layers_02_01_04_06

theorem cells_02_01_04_06 : QTableValid (![2, 3, 7, 13] : Fin 4 → ℕ) layers_02_01_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_04_06

theorem valid_02_01_04_06 :
    SparseRowValid (![2, 3, 7, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 7, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 7 + 13 = 25
      decide
    have hzsq : (∑ i, (((![2, 3, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 7^2 + 13^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_04_06
#print axioms Paper7MomentGapNumeric.valid_02_01_04_06

def qvalues_02_01_04_06 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_04_06

theorem row_02_01_04_06 : b4RowContribution (![2, 3, 7, 13] : Fin 4 → ℕ) = 105 := by
  calc
    b4RowContribution (![2, 3, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_04_06) :=
      sparseRow_sound (![2, 3, 7, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_04_06) valid_02_01_04_06
    _ = 105 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_04_06 Q := by
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
        _ = 105 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_04_06

theorem weighted_02_01_04_06 : b4RawGapContribution ![2, 1, 4, 6] = 2520 := by
  calc
    b4RawGapContribution ![2, 1, 4, 6] = b4GapPatternWeight 1 4 6 * 105 :=
      b4GapContribution_from_row 2 1 4 6 105 row_02_01_04_06
    _ = 2520 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_06

theorem row_02_01_04_07 : b4RowContribution (![2, 3, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 14 = 26
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 14^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_07

theorem weighted_02_01_04_07 : b4RawGapContribution ![2, 1, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 7] = b4GapPatternWeight 1 4 7 * 0 :=
      b4GapContribution_from_row 2 1 4 7 0 row_02_01_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_07

def layers_02_01_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 77, 86, 92, 95, 96, 96, 96, 96, 95, 92, 86]]
#print axioms Paper7MomentGapNumeric.layers_02_01_04_08

theorem cells_02_01_04_08 : QTableValid (![2, 3, 7, 15] : Fin 4 → ℕ) layers_02_01_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_04_08

theorem valid_02_01_04_08 :
    SparseRowValid (![2, 3, 7, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_01_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 7, 15] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 7 + 15 = 27
      decide
    have hzsq : (∑ i, (((![2, 3, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 287 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 7^2 + 15^2 = 287
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_04_08
#print axioms Paper7MomentGapNumeric.valid_02_01_04_08

def qvalues_02_01_04_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_04_08

theorem row_02_01_04_08 : b4RowContribution (![2, 3, 7, 15] : Fin 4 → ℕ) = 77 := by
  calc
    b4RowContribution (![2, 3, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_02_01_04_08) :=
      sparseRow_sound (![2, 3, 7, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_01_04_08) valid_02_01_04_08
    _ = 77 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_04_08 Q := by
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
        _ = 77 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_04_08

theorem weighted_02_01_04_08 : b4RawGapContribution ![2, 1, 4, 8] = 1848 := by
  calc
    b4RawGapContribution ![2, 1, 4, 8] = b4GapPatternWeight 1 4 8 * 77 :=
      b4GapContribution_from_row 2 1 4 8 77 row_02_01_04_08
    _ = 1848 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_08

theorem row_02_01_04_09 : b4RowContribution (![2, 3, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 16 = 28
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 16^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_09

theorem weighted_02_01_04_09 : b4RawGapContribution ![2, 1, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 9] = b4GapPatternWeight 1 4 9 * 0 :=
      b4GapContribution_from_row 2 1 4 9 0 row_02_01_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_09

theorem row_02_01_04_10 : b4RowContribution (![2, 3, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 17 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 17^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_10

theorem weighted_02_01_04_10 : b4RawGapContribution ![2, 1, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 10] = b4GapPatternWeight 1 4 10 * 0 :=
      b4GapContribution_from_row 2 1 4 10 0 row_02_01_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_10

theorem row_02_01_04_11 : b4RowContribution (![2, 3, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 18 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 18^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_11

theorem weighted_02_01_04_11 : b4RawGapContribution ![2, 1, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 11] = b4GapPatternWeight 1 4 11 * 0 :=
      b4GapContribution_from_row 2 1 4 11 0 row_02_01_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_11

theorem row_02_01_04_12 : b4RowContribution (![2, 3, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 19 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 19^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_12

theorem weighted_02_01_04_12 : b4RawGapContribution ![2, 1, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 12] = b4GapPatternWeight 1 4 12 * 0 :=
      b4GapContribution_from_row 2 1 4 12 0 row_02_01_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_12

theorem row_02_01_04_13 : b4RowContribution (![2, 3, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 20 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 20^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_13

theorem weighted_02_01_04_13 : b4RawGapContribution ![2, 1, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 13] = b4GapPatternWeight 1 4 13 * 0 :=
      b4GapContribution_from_row 2 1 4 13 0 row_02_01_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_13

theorem row_02_01_04_14 : b4RowContribution (![2, 3, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 21 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 503 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 21^2 = 503
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_14

theorem weighted_02_01_04_14 : b4RawGapContribution ![2, 1, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 14] = b4GapPatternWeight 1 4 14 * 0 :=
      b4GapContribution_from_row 2 1 4 14 0 row_02_01_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_14

theorem row_02_01_04_15 : b4RowContribution (![2, 3, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 22 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 22^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_15

theorem weighted_02_01_04_15 : b4RawGapContribution ![2, 1, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 15] = b4GapPatternWeight 1 4 15 * 0 :=
      b4GapContribution_from_row 2 1 4 15 0 row_02_01_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_15

theorem row_02_01_04_16 : b4RowContribution (![2, 3, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 23 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 591 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 23^2 = 591
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_16

theorem weighted_02_01_04_16 : b4RawGapContribution ![2, 1, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 16] = b4GapPatternWeight 1 4 16 * 0 :=
      b4GapContribution_from_row 2 1 4 16 0 row_02_01_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_16

theorem row_02_01_04_17 : b4RowContribution (![2, 3, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 24 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 638 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 24^2 = 638
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_17

theorem weighted_02_01_04_17 : b4RawGapContribution ![2, 1, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 17] = b4GapPatternWeight 1 4 17 * 0 :=
      b4GapContribution_from_row 2 1 4 17 0 row_02_01_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_17

theorem row_02_01_04_18 : b4RowContribution (![2, 3, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 7, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 7 + 25 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 687 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 7^2 + 25^2 = 687
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_04_18

theorem weighted_02_01_04_18 : b4RawGapContribution ![2, 1, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 4, 18] = b4GapPatternWeight 1 4 18 * 0 :=
      b4GapContribution_from_row 2 1 4 18 0 row_02_01_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_04_18

def dvalues_02_01_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 2520, 0, 1848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_04

theorem dblock_02_01_04 : b4GapPatternDBlock 2 1 4 = 4368 := by
  calc
    b4GapPatternDBlock 2 1 4 = ∑ d : Fin 19, dvalues_02_01_04 d := by
      apply b4GapDBlock_of_rows 2 1 4 dvalues_02_01_04
      intro d
      fin_cases d
      · exact weighted_02_01_04_00
      · exact weighted_02_01_04_01
      · exact weighted_02_01_04_02
      · exact weighted_02_01_04_03
      · exact weighted_02_01_04_04
      · exact weighted_02_01_04_05
      · exact weighted_02_01_04_06
      · exact weighted_02_01_04_07
      · exact weighted_02_01_04_08
      · exact weighted_02_01_04_09
      · exact weighted_02_01_04_10
      · exact weighted_02_01_04_11
      · exact weighted_02_01_04_12
      · exact weighted_02_01_04_13
      · exact weighted_02_01_04_14
      · exact weighted_02_01_04_15
      · exact weighted_02_01_04_16
      · exact weighted_02_01_04_17
      · exact weighted_02_01_04_18
    _ = 4368 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_04

end Paper7MomentGapNumeric
