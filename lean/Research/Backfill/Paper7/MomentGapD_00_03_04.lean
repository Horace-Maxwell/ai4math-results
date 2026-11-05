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

theorem row_00_03_04_00 : b4RowContribution (![0, 3, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 7 = 17
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 107 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 7^2 = 107
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_00

theorem weighted_00_03_04_00 : b4RawGapContribution ![0, 3, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 0] = b4GapPatternWeight 3 4 0 * 0 :=
      b4GapContribution_from_row 0 3 4 0 0 row_00_03_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_00

theorem row_00_03_04_01 : b4RowContribution (![0, 3, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 8 = 18
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 8^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_01

theorem weighted_00_03_04_01 : b4RawGapContribution ![0, 3, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 1] = b4GapPatternWeight 3 4 1 * 0 :=
      b4GapContribution_from_row 0 3 4 1 0 row_00_03_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_01

theorem row_00_03_04_02 : b4RowContribution (![0, 3, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 9 = 19
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 9^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_02

theorem weighted_00_03_04_02 : b4RawGapContribution ![0, 3, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 2] = b4GapPatternWeight 3 4 2 * 0 :=
      b4GapContribution_from_row 0 3 4 2 0 row_00_03_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_02

def layers_00_03_04_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 29, 31, 32, 31, 29, 26, 22, 18, 14, 10, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_03_04_03

theorem cells_00_03_04_03 : QTableValid (![0, 3, 7, 10] : Fin 4 → ℕ) layers_00_03_04_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_04_03

theorem valid_00_03_04_03 :
    SparseRowValid (![0, 3, 7, 10] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_03_04_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 7, 10] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 7 + 10 = 20
      decide
    have hzsq : (∑ i, (((![0, 3, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 158 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 7^2 + 10^2 = 158
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_04_03
#print axioms Paper7MomentGapNumeric.valid_00_03_04_03

def qvalues_00_03_04_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_04_03

theorem row_00_03_04_03 : b4RowContribution (![0, 3, 7, 10] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![0, 3, 7, 10] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_00_03_04_03) :=
      sparseRow_sound (![0, 3, 7, 10] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_03_04_03) valid_00_03_04_03
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_04_03 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_04_03

theorem weighted_00_03_04_03 : b4RawGapContribution ![0, 3, 4, 3] = 240 := by
  calc
    b4RawGapContribution ![0, 3, 4, 3] = b4GapPatternWeight 3 4 3 * 10 :=
      b4GapContribution_from_row 0 3 4 3 10 row_00_03_04_03
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_03

theorem row_00_03_04_04 : b4RowContribution (![0, 3, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 11 = 21
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 179 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 11^2 = 179
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_04

theorem weighted_00_03_04_04 : b4RawGapContribution ![0, 3, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 4] = b4GapPatternWeight 3 4 4 * 0 :=
      b4GapContribution_from_row 0 3 4 4 0 row_00_03_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_04

theorem row_00_03_04_05 : b4RowContribution (![0, 3, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 12 = 22
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 12^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_05

theorem weighted_00_03_04_05 : b4RawGapContribution ![0, 3, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 5] = b4GapPatternWeight 3 4 5 * 0 :=
      b4GapContribution_from_row 0 3 4 5 0 row_00_03_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_05

def layers_00_03_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 29, 31, 32, 32, 32, 32, 31, 29, 26, 22, 18]]
#print axioms Paper7MomentGapNumeric.layers_00_03_04_06

theorem cells_00_03_04_06 : QTableValid (![0, 3, 7, 13] : Fin 4 → ℕ) layers_00_03_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_04_06

theorem valid_00_03_04_06 :
    SparseRowValid (![0, 3, 7, 13] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_03_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 7, 13] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 7 + 13 = 23
      decide
    have hzsq : (∑ i, (((![0, 3, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 7^2 + 13^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_04_06
#print axioms Paper7MomentGapNumeric.valid_00_03_04_06

def qvalues_00_03_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_04_06

theorem row_00_03_04_06 : b4RowContribution (![0, 3, 7, 13] : Fin 4 → ℕ) = 60 := by
  calc
    b4RowContribution (![0, 3, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_03_04_06) :=
      sparseRow_sound (![0, 3, 7, 13] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_03_04_06) valid_00_03_04_06
    _ = 60 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_04_06 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_04_06

theorem weighted_00_03_04_06 : b4RawGapContribution ![0, 3, 4, 6] = 1440 := by
  calc
    b4RawGapContribution ![0, 3, 4, 6] = b4GapPatternWeight 3 4 6 * 60 :=
      b4GapContribution_from_row 0 3 4 6 60 row_00_03_04_06
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_06

theorem row_00_03_04_07 : b4RowContribution (![0, 3, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 14] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 14 = 24
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 14^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_07

theorem weighted_00_03_04_07 : b4RawGapContribution ![0, 3, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 7] = b4GapPatternWeight 3 4 7 * 0 :=
      b4GapContribution_from_row 0 3 4 7 0 row_00_03_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_07

def layers_00_03_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 29, 31, 32, 32, 32, 32, 32, 32, 31, 29, 26]]
#print axioms Paper7MomentGapNumeric.layers_00_03_04_08

theorem cells_00_03_04_08 : QTableValid (![0, 3, 7, 15] : Fin 4 → ℕ) layers_00_03_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_04_08

theorem valid_00_03_04_08 :
    SparseRowValid (![0, 3, 7, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_03_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 7, 15] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 7 + 15 = 25
      decide
    have hzsq : (∑ i, (((![0, 3, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 7^2 + 15^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_04_08
#print axioms Paper7MomentGapNumeric.valid_00_03_04_08

def qvalues_00_03_04_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_04_08

theorem row_00_03_04_08 : b4RowContribution (![0, 3, 7, 15] : Fin 4 → ℕ) = 26 := by
  calc
    b4RowContribution (![0, 3, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_03_04_08) :=
      sparseRow_sound (![0, 3, 7, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_03_04_08) valid_00_03_04_08
    _ = 26 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_04_08 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 26 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_04_08

theorem weighted_00_03_04_08 : b4RawGapContribution ![0, 3, 4, 8] = 624 := by
  calc
    b4RawGapContribution ![0, 3, 4, 8] = b4GapPatternWeight 3 4 8 * 26 :=
      b4GapContribution_from_row 0 3 4 8 26 row_00_03_04_08
    _ = 624 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_08

theorem row_00_03_04_09 : b4RowContribution (![0, 3, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 16 = 26
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 16^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_09

theorem weighted_00_03_04_09 : b4RawGapContribution ![0, 3, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 9] = b4GapPatternWeight 3 4 9 * 0 :=
      b4GapContribution_from_row 0 3 4 9 0 row_00_03_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_09

theorem row_00_03_04_10 : b4RowContribution (![0, 3, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 17 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 17^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_10

theorem weighted_00_03_04_10 : b4RawGapContribution ![0, 3, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 10] = b4GapPatternWeight 3 4 10 * 0 :=
      b4GapContribution_from_row 0 3 4 10 0 row_00_03_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_10

theorem row_00_03_04_11 : b4RowContribution (![0, 3, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 18 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 18^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_11

theorem weighted_00_03_04_11 : b4RawGapContribution ![0, 3, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 11] = b4GapPatternWeight 3 4 11 * 0 :=
      b4GapContribution_from_row 0 3 4 11 0 row_00_03_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_11

theorem row_00_03_04_12 : b4RowContribution (![0, 3, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 19 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 19^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_12

theorem weighted_00_03_04_12 : b4RawGapContribution ![0, 3, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 12] = b4GapPatternWeight 3 4 12 * 0 :=
      b4GapContribution_from_row 0 3 4 12 0 row_00_03_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_12

theorem row_00_03_04_13 : b4RowContribution (![0, 3, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 20 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 20^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_13

theorem weighted_00_03_04_13 : b4RawGapContribution ![0, 3, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 13] = b4GapPatternWeight 3 4 13 * 0 :=
      b4GapContribution_from_row 0 3 4 13 0 row_00_03_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_13

theorem row_00_03_04_14 : b4RowContribution (![0, 3, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 21 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 499 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 21^2 = 499
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_14

theorem weighted_00_03_04_14 : b4RawGapContribution ![0, 3, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 14] = b4GapPatternWeight 3 4 14 * 0 :=
      b4GapContribution_from_row 0 3 4 14 0 row_00_03_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_14

theorem row_00_03_04_15 : b4RowContribution (![0, 3, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 22 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 542 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 22^2 = 542
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_15

theorem weighted_00_03_04_15 : b4RawGapContribution ![0, 3, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 15] = b4GapPatternWeight 3 4 15 * 0 :=
      b4GapContribution_from_row 0 3 4 15 0 row_00_03_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_15

theorem row_00_03_04_16 : b4RowContribution (![0, 3, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 23 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 23^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_16

theorem weighted_00_03_04_16 : b4RawGapContribution ![0, 3, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 16] = b4GapPatternWeight 3 4 16 * 0 :=
      b4GapContribution_from_row 0 3 4 16 0 row_00_03_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_16

theorem row_00_03_04_17 : b4RowContribution (![0, 3, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 24 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 634 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 24^2 = 634
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_17

theorem weighted_00_03_04_17 : b4RawGapContribution ![0, 3, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 17] = b4GapPatternWeight 3 4 17 * 0 :=
      b4GapContribution_from_row 0 3 4 17 0 row_00_03_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_17

theorem row_00_03_04_18 : b4RowContribution (![0, 3, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 25 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 683 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 25^2 = 683
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_18

theorem weighted_00_03_04_18 : b4RawGapContribution ![0, 3, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 18] = b4GapPatternWeight 3 4 18 * 0 :=
      b4GapContribution_from_row 0 3 4 18 0 row_00_03_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_18

theorem row_00_03_04_19 : b4RowContribution (![0, 3, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 26 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 734 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 26^2 = 734
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_19

theorem weighted_00_03_04_19 : b4RawGapContribution ![0, 3, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 19] = b4GapPatternWeight 3 4 19 * 0 :=
      b4GapContribution_from_row 0 3 4 19 0 row_00_03_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_19

theorem row_00_03_04_20 : b4RowContribution (![0, 3, 7, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 7, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 7 + 27 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 7, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 787 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 7^2 + 27^2 = 787
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_04_20

theorem weighted_00_03_04_20 : b4RawGapContribution ![0, 3, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 4, 20] = b4GapPatternWeight 3 4 20 * 0 :=
      b4GapContribution_from_row 0 3 4 20 0 row_00_03_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_04_20

def dvalues_00_03_04 : Fin 21 → ℕ := ![0, 0, 0, 240, 0, 0, 1440, 0, 624, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_04

theorem dblock_00_03_04 : b4GapPatternDBlock 0 3 4 = 2304 := by
  calc
    b4GapPatternDBlock 0 3 4 = ∑ d : Fin 21, dvalues_00_03_04 d := by
      apply b4GapDBlock_of_rows 0 3 4 dvalues_00_03_04
      intro d
      fin_cases d
      · exact weighted_00_03_04_00
      · exact weighted_00_03_04_01
      · exact weighted_00_03_04_02
      · exact weighted_00_03_04_03
      · exact weighted_00_03_04_04
      · exact weighted_00_03_04_05
      · exact weighted_00_03_04_06
      · exact weighted_00_03_04_07
      · exact weighted_00_03_04_08
      · exact weighted_00_03_04_09
      · exact weighted_00_03_04_10
      · exact weighted_00_03_04_11
      · exact weighted_00_03_04_12
      · exact weighted_00_03_04_13
      · exact weighted_00_03_04_14
      · exact weighted_00_03_04_15
      · exact weighted_00_03_04_16
      · exact weighted_00_03_04_17
      · exact weighted_00_03_04_18
      · exact weighted_00_03_04_19
      · exact weighted_00_03_04_20
    _ = 2304 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_04

end Paper7MomentGapNumeric
