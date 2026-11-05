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

theorem row_00_02_05_00 : b4RowContribution (![0, 2, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 7 = 16
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 102 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 7^2 = 102
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_00

theorem weighted_00_02_05_00 : b4RawGapContribution ![0, 2, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 0] = b4GapPatternWeight 2 5 0 * 0 :=
      b4GapContribution_from_row 0 2 5 0 0 row_00_02_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_00

theorem row_00_02_05_01 : b4RowContribution (![0, 2, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 8 = 17
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 117 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 8^2 = 117
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_01

theorem weighted_00_02_05_01 : b4RawGapContribution ![0, 2, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 1] = b4GapPatternWeight 2 5 1 * 0 :=
      b4GapContribution_from_row 0 2 5 1 0 row_00_02_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_01

theorem row_00_02_05_02 : b4RowContribution (![0, 2, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 9 = 18
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 134 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 9^2 = 134
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_02

theorem weighted_00_02_05_02 : b4RawGapContribution ![0, 2, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 2] = b4GapPatternWeight 2 5 2 * 0 :=
      b4GapContribution_from_row 0 2 5 2 0 row_00_02_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_02

theorem row_00_02_05_03 : b4RowContribution (![0, 2, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 10 = 19
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 10^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_03

theorem weighted_00_02_05_03 : b4RawGapContribution ![0, 2, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 3] = b4GapPatternWeight 2 5 3 * 0 :=
      b4GapContribution_from_row 0 2 5 3 0 row_00_02_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_03

def layers_00_02_05_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 24, 24, 23, 21, 18, 15, 12, 9, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_02_05_04

theorem cells_00_02_05_04 : QTableValid (![0, 2, 7, 11] : Fin 4 → ℕ) layers_00_02_05_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_05_04

theorem valid_00_02_05_04 :
    SparseRowValid (![0, 2, 7, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_05_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 7, 11] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 7 + 11 = 20
      decide
    have hzsq : (∑ i, (((![0, 2, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 7^2 + 11^2 = 174
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_05_04
#print axioms Paper7MomentGapNumeric.valid_00_02_05_04

def qvalues_00_02_05_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_05_04

theorem row_00_02_05_04 : b4RowContribution (![0, 2, 7, 11] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_02_05_04) :=
      sparseRow_sound (![0, 2, 7, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_05_04) valid_00_02_05_04
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_05_04 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_05_04

theorem weighted_00_02_05_04 : b4RawGapContribution ![0, 2, 5, 4] = 576 := by
  calc
    b4RawGapContribution ![0, 2, 5, 4] = b4GapPatternWeight 2 5 4 * 24 :=
      b4GapContribution_from_row 0 2 5 4 24 row_00_02_05_04
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_04

theorem row_00_02_05_05 : b4RowContribution (![0, 2, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 12 = 21
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 12^2 = 197
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_05

theorem weighted_00_02_05_05 : b4RawGapContribution ![0, 2, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 5] = b4GapPatternWeight 2 5 5 * 0 :=
      b4GapContribution_from_row 0 2 5 5 0 row_00_02_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_05

def layers_00_02_05_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 24, 24, 24, 24, 23, 21, 18, 15, 12]]
#print axioms Paper7MomentGapNumeric.layers_00_02_05_06

theorem cells_00_02_05_06 : QTableValid (![0, 2, 7, 13] : Fin 4 → ℕ) layers_00_02_05_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_05_06

theorem valid_00_02_05_06 :
    SparseRowValid (![0, 2, 7, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_05_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 7, 13] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 7 + 13 = 22
      decide
    have hzsq : (∑ i, (((![0, 2, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 7^2 + 13^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_05_06
#print axioms Paper7MomentGapNumeric.valid_00_02_05_06

def qvalues_00_02_05_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_05_06

theorem row_00_02_05_06 : b4RowContribution (![0, 2, 7, 13] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_02_05_06) :=
      sparseRow_sound (![0, 2, 7, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_05_06) valid_00_02_05_06
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_05_06 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_05_06

theorem weighted_00_02_05_06 : b4RawGapContribution ![0, 2, 5, 6] = 576 := by
  calc
    b4RawGapContribution ![0, 2, 5, 6] = b4GapPatternWeight 2 5 6 * 24 :=
      b4GapContribution_from_row 0 2 5 6 24 row_00_02_05_06
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_06

theorem row_00_02_05_07 : b4RowContribution (![0, 2, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 14] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 14 = 23
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 14^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_07

theorem weighted_00_02_05_07 : b4RawGapContribution ![0, 2, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 7] = b4GapPatternWeight 2 5 7 * 0 :=
      b4GapContribution_from_row 0 2 5 7 0 row_00_02_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_07

def layers_00_02_05_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 24, 24, 24, 24, 24, 24, 23, 21, 18]]
#print axioms Paper7MomentGapNumeric.layers_00_02_05_08

theorem cells_00_02_05_08 : QTableValid (![0, 2, 7, 15] : Fin 4 → ℕ) layers_00_02_05_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_05_08

theorem valid_00_02_05_08 :
    SparseRowValid (![0, 2, 7, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_02_05_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 7, 15] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 7 + 15 = 24
      decide
    have hzsq : (∑ i, (((![0, 2, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 7^2 + 15^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_05_08
#print axioms Paper7MomentGapNumeric.valid_00_02_05_08

def qvalues_00_02_05_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_05_08

theorem row_00_02_05_08 : b4RowContribution (![0, 2, 7, 15] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_02_05_08) :=
      sparseRow_sound (![0, 2, 7, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_02_05_08) valid_00_02_05_08
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_05_08 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_05_08

theorem weighted_00_02_05_08 : b4RawGapContribution ![0, 2, 5, 8] = 576 := by
  calc
    b4RawGapContribution ![0, 2, 5, 8] = b4GapPatternWeight 2 5 8 * 24 :=
      b4GapContribution_from_row 0 2 5 8 24 row_00_02_05_08
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_08

theorem row_00_02_05_09 : b4RowContribution (![0, 2, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 16] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 16 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 16^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_09

theorem weighted_00_02_05_09 : b4RawGapContribution ![0, 2, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 9] = b4GapPatternWeight 2 5 9 * 0 :=
      b4GapContribution_from_row 0 2 5 9 0 row_00_02_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_09

theorem row_00_02_05_10 : b4RowContribution (![0, 2, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 17 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 17^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_10

theorem weighted_00_02_05_10 : b4RawGapContribution ![0, 2, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 10] = b4GapPatternWeight 2 5 10 * 0 :=
      b4GapContribution_from_row 0 2 5 10 0 row_00_02_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_10

theorem row_00_02_05_11 : b4RowContribution (![0, 2, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 18 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 18^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_11

theorem weighted_00_02_05_11 : b4RawGapContribution ![0, 2, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 11] = b4GapPatternWeight 2 5 11 * 0 :=
      b4GapContribution_from_row 0 2 5 11 0 row_00_02_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_11

theorem row_00_02_05_12 : b4RowContribution (![0, 2, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 19 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 19^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_12

theorem weighted_00_02_05_12 : b4RawGapContribution ![0, 2, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 12] = b4GapPatternWeight 2 5 12 * 0 :=
      b4GapContribution_from_row 0 2 5 12 0 row_00_02_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_12

theorem row_00_02_05_13 : b4RowContribution (![0, 2, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 20 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 20^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_13

theorem weighted_00_02_05_13 : b4RawGapContribution ![0, 2, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 13] = b4GapPatternWeight 2 5 13 * 0 :=
      b4GapContribution_from_row 0 2 5 13 0 row_00_02_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_13

theorem row_00_02_05_14 : b4RowContribution (![0, 2, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 21 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 21^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_14

theorem weighted_00_02_05_14 : b4RawGapContribution ![0, 2, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 14] = b4GapPatternWeight 2 5 14 * 0 :=
      b4GapContribution_from_row 0 2 5 14 0 row_00_02_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_14

theorem row_00_02_05_15 : b4RowContribution (![0, 2, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 22 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 537 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 22^2 = 537
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_15

theorem weighted_00_02_05_15 : b4RawGapContribution ![0, 2, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 15] = b4GapPatternWeight 2 5 15 * 0 :=
      b4GapContribution_from_row 0 2 5 15 0 row_00_02_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_15

theorem row_00_02_05_16 : b4RowContribution (![0, 2, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 23 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 582 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 23^2 = 582
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_16

theorem weighted_00_02_05_16 : b4RawGapContribution ![0, 2, 5, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 16] = b4GapPatternWeight 2 5 16 * 0 :=
      b4GapContribution_from_row 0 2 5 16 0 row_00_02_05_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_16

theorem row_00_02_05_17 : b4RowContribution (![0, 2, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 24 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 629 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 24^2 = 629
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_17

theorem weighted_00_02_05_17 : b4RawGapContribution ![0, 2, 5, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 17] = b4GapPatternWeight 2 5 17 * 0 :=
      b4GapContribution_from_row 0 2 5 17 0 row_00_02_05_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_17

theorem row_00_02_05_18 : b4RowContribution (![0, 2, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 25 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 678 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 25^2 = 678
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_18

theorem weighted_00_02_05_18 : b4RawGapContribution ![0, 2, 5, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 18] = b4GapPatternWeight 2 5 18 * 0 :=
      b4GapContribution_from_row 0 2 5 18 0 row_00_02_05_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_18

theorem row_00_02_05_19 : b4RowContribution (![0, 2, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 26 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 729 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 26^2 = 729
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_19

theorem weighted_00_02_05_19 : b4RawGapContribution ![0, 2, 5, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 19] = b4GapPatternWeight 2 5 19 * 0 :=
      b4GapContribution_from_row 0 2 5 19 0 row_00_02_05_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_19

theorem row_00_02_05_20 : b4RowContribution (![0, 2, 7, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 27 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 782 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 27^2 = 782
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_20

theorem weighted_00_02_05_20 : b4RawGapContribution ![0, 2, 5, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 20] = b4GapPatternWeight 2 5 20 * 0 :=
      b4GapContribution_from_row 0 2 5 20 0 row_00_02_05_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_20

theorem row_00_02_05_21 : b4RowContribution (![0, 2, 7, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 7, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 7 + 28 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 7, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 837 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 7^2 + 28^2 = 837
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_05_21

theorem weighted_00_02_05_21 : b4RawGapContribution ![0, 2, 5, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 5, 21] = b4GapPatternWeight 2 5 21 * 0 :=
      b4GapContribution_from_row 0 2 5 21 0 row_00_02_05_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_05_21

def dvalues_00_02_05 : Fin 22 → ℕ := ![0, 0, 0, 0, 576, 0, 576, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_05

theorem dblock_00_02_05 : b4GapPatternDBlock 0 2 5 = 1728 := by
  calc
    b4GapPatternDBlock 0 2 5 = ∑ d : Fin 22, dvalues_00_02_05 d := by
      apply b4GapDBlock_of_rows 0 2 5 dvalues_00_02_05
      intro d
      fin_cases d
      · exact weighted_00_02_05_00
      · exact weighted_00_02_05_01
      · exact weighted_00_02_05_02
      · exact weighted_00_02_05_03
      · exact weighted_00_02_05_04
      · exact weighted_00_02_05_05
      · exact weighted_00_02_05_06
      · exact weighted_00_02_05_07
      · exact weighted_00_02_05_08
      · exact weighted_00_02_05_09
      · exact weighted_00_02_05_10
      · exact weighted_00_02_05_11
      · exact weighted_00_02_05_12
      · exact weighted_00_02_05_13
      · exact weighted_00_02_05_14
      · exact weighted_00_02_05_15
      · exact weighted_00_02_05_16
      · exact weighted_00_02_05_17
      · exact weighted_00_02_05_18
      · exact weighted_00_02_05_19
      · exact weighted_00_02_05_20
      · exact weighted_00_02_05_21
    _ = 1728 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_05

end Paper7MomentGapNumeric
