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

theorem row_00_04_00_00 : b4RowContribution (![0, 4, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 4] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 4 = 12
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 48 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 4^2 = 48
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_00

theorem weighted_00_04_00_00 : b4RawGapContribution ![0, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 0 4 0 0 0 row_00_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_00

theorem row_00_04_00_01 : b4RowContribution (![0, 4, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 5 = 13
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 57 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 5^2 = 57
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_01

theorem weighted_00_04_00_01 : b4RawGapContribution ![0, 4, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 0 :=
      b4GapContribution_from_row 0 4 0 1 0 row_00_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_01

theorem row_00_04_00_02 : b4RowContribution (![0, 4, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 6 = 14
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 68 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 6^2 = 68
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_02

theorem weighted_00_04_00_02 : b4RawGapContribution ![0, 4, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 2] = b4GapPatternWeight 4 0 2 * 0 :=
      b4GapContribution_from_row 0 4 0 2 0 row_00_04_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_02

theorem row_00_04_00_03 : b4RowContribution (![0, 4, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 7 = 15
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 7^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_03

theorem weighted_00_04_00_03 : b4RawGapContribution ![0, 4, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 3] = b4GapPatternWeight 4 0 3 * 0 :=
      b4GapContribution_from_row 0 4 0 3 0 row_00_04_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_03

theorem row_00_04_00_04 : b4RowContribution (![0, 4, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 8 = 16
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 96 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 8^2 = 96
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_04

theorem weighted_00_04_00_04 : b4RawGapContribution ![0, 4, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 4] = b4GapPatternWeight 4 0 4 * 0 :=
      b4GapContribution_from_row 0 4 0 4 0 row_00_04_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_04

theorem row_00_04_00_05 : b4RowContribution (![0, 4, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 9 = 17
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 113 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 9^2 = 113
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_05

theorem weighted_00_04_00_05 : b4RawGapContribution ![0, 4, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 5] = b4GapPatternWeight 4 0 5 * 0 :=
      b4GapContribution_from_row 0 4 0 5 0 row_00_04_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_05

theorem row_00_04_00_06 : b4RowContribution (![0, 4, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 10 = 18
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 10^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_06

theorem weighted_00_04_00_06 : b4RawGapContribution ![0, 4, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 6] = b4GapPatternWeight 4 0 6 * 0 :=
      b4GapContribution_from_row 0 4 0 6 0 row_00_04_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_06

theorem row_00_04_00_07 : b4RowContribution (![0, 4, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 11] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 11 = 19
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 11^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_07

theorem weighted_00_04_00_07 : b4RawGapContribution ![0, 4, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 7] = b4GapPatternWeight 4 0 7 * 0 :=
      b4GapContribution_from_row 0 4 0 7 0 row_00_04_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_07

def layers_00_04_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 25, 25, 24, 22, 19, 15, 10, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_04_00_08

theorem cells_00_04_00_08 : QTableValid (![0, 4, 4, 12] : Fin 4 → ℕ) layers_00_04_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_00_08

theorem valid_00_04_00_08 :
    SparseRowValid (![0, 4, 4, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 4, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 4 + 12 = 20
      decide
    have hzsq : (∑ i, (((![0, 4, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 176 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 4^2 + 12^2 = 176
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_00_08
#print axioms Paper7MomentGapNumeric.valid_00_04_00_08

def qvalues_00_04_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_00_08

theorem row_00_04_00_08 : b4RowContribution (![0, 4, 4, 12] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![0, 4, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_04_00_08) :=
      sparseRow_sound (![0, 4, 4, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_00_08) valid_00_04_00_08
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_00_08 Q := by
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
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_00_08

theorem weighted_00_04_00_08 : b4RawGapContribution ![0, 4, 0, 8] = 300 := by
  calc
    b4RawGapContribution ![0, 4, 0, 8] = b4GapPatternWeight 4 0 8 * 25 :=
      b4GapContribution_from_row 0 4 0 8 25 row_00_04_00_08
    _ = 300 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_08

theorem row_00_04_00_09 : b4RowContribution (![0, 4, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 13] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 13 = 21
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 13^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_09

theorem weighted_00_04_00_09 : b4RawGapContribution ![0, 4, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 9] = b4GapPatternWeight 4 0 9 * 0 :=
      b4GapContribution_from_row 0 4 0 9 0 row_00_04_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_09

def layers_00_04_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 25, 25, 25, 25, 24, 22, 19, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_04_00_10

theorem cells_00_04_00_10 : QTableValid (![0, 4, 4, 14] : Fin 4 → ℕ) layers_00_04_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_00_10

theorem valid_00_04_00_10 :
    SparseRowValid (![0, 4, 4, 14] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_04_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 4, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 4 + 14 = 22
      decide
    have hzsq : (∑ i, (((![0, 4, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 4^2 + 14^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_00_10
#print axioms Paper7MomentGapNumeric.valid_00_04_00_10

def qvalues_00_04_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 24, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_00_10

theorem row_00_04_00_10 : b4RowContribution (![0, 4, 4, 14] : Fin 4 → ℕ) = 49 := by
  calc
    b4RowContribution (![0, 4, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_04_00_10) :=
      sparseRow_sound (![0, 4, 4, 14] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_04_00_10) valid_00_04_00_10
    _ = 49 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_00_10 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 49 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_00_10

theorem weighted_00_04_00_10 : b4RawGapContribution ![0, 4, 0, 10] = 588 := by
  calc
    b4RawGapContribution ![0, 4, 0, 10] = b4GapPatternWeight 4 0 10 * 49 :=
      b4GapContribution_from_row 0 4 0 10 49 row_00_04_00_10
    _ = 588 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_10

theorem row_00_04_00_11 : b4RowContribution (![0, 4, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 15 = 23
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 15^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_11

theorem weighted_00_04_00_11 : b4RawGapContribution ![0, 4, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 11] = b4GapPatternWeight 4 0 11 * 0 :=
      b4GapContribution_from_row 0 4 0 11 0 row_00_04_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_11

def layers_00_04_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 24, 22]]
#print axioms Paper7MomentGapNumeric.layers_00_04_00_12

theorem cells_00_04_00_12 : QTableValid (![0, 4, 4, 16] : Fin 4 → ℕ) layers_00_04_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_00_12

theorem valid_00_04_00_12 :
    SparseRowValid (![0, 4, 4, 16] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_04_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 4, 16] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 4 + 16 = 24
      decide
    have hzsq : (∑ i, (((![0, 4, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 288 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 4^2 + 16^2 = 288
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_00_12
#print axioms Paper7MomentGapNumeric.valid_00_04_00_12

def qvalues_00_04_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_00_12

theorem row_00_04_00_12 : b4RowContribution (![0, 4, 4, 16] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![0, 4, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_04_00_12) :=
      sparseRow_sound (![0, 4, 4, 16] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_04_00_12) valid_00_04_00_12
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_00_12 Q := by
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
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_00_12

theorem weighted_00_04_00_12 : b4RawGapContribution ![0, 4, 0, 12] = 564 := by
  calc
    b4RawGapContribution ![0, 4, 0, 12] = b4GapPatternWeight 4 0 12 * 47 :=
      b4GapContribution_from_row 0 4 0 12 47 row_00_04_00_12
    _ = 564 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_12

theorem row_00_04_00_13 : b4RowContribution (![0, 4, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 17 = 25
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 17^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_13

theorem weighted_00_04_00_13 : b4RawGapContribution ![0, 4, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 13] = b4GapPatternWeight 4 0 13 * 0 :=
      b4GapContribution_from_row 0 4 0 13 0 row_00_04_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_13

theorem row_00_04_00_14 : b4RowContribution (![0, 4, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 18 = 26
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 18^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_14

theorem weighted_00_04_00_14 : b4RawGapContribution ![0, 4, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 14] = b4GapPatternWeight 4 0 14 * 0 :=
      b4GapContribution_from_row 0 4 0 14 0 row_00_04_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_14

theorem row_00_04_00_15 : b4RowContribution (![0, 4, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 19 = 27
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 19^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_15

theorem weighted_00_04_00_15 : b4RawGapContribution ![0, 4, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 15] = b4GapPatternWeight 4 0 15 * 0 :=
      b4GapContribution_from_row 0 4 0 15 0 row_00_04_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_15

theorem row_00_04_00_16 : b4RowContribution (![0, 4, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 20 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 432 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 20^2 = 432
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_16

theorem weighted_00_04_00_16 : b4RawGapContribution ![0, 4, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 16] = b4GapPatternWeight 4 0 16 * 0 :=
      b4GapContribution_from_row 0 4 0 16 0 row_00_04_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_16

theorem row_00_04_00_17 : b4RowContribution (![0, 4, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 21 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 21^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_17

theorem weighted_00_04_00_17 : b4RawGapContribution ![0, 4, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 17] = b4GapPatternWeight 4 0 17 * 0 :=
      b4GapContribution_from_row 0 4 0 17 0 row_00_04_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_17

theorem row_00_04_00_18 : b4RowContribution (![0, 4, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 22 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 516 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 22^2 = 516
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_18

theorem weighted_00_04_00_18 : b4RawGapContribution ![0, 4, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 18] = b4GapPatternWeight 4 0 18 * 0 :=
      b4GapContribution_from_row 0 4 0 18 0 row_00_04_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_18

theorem row_00_04_00_19 : b4RowContribution (![0, 4, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 23 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 561 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 23^2 = 561
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_19

theorem weighted_00_04_00_19 : b4RawGapContribution ![0, 4, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 19] = b4GapPatternWeight 4 0 19 * 0 :=
      b4GapContribution_from_row 0 4 0 19 0 row_00_04_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_19

theorem row_00_04_00_20 : b4RowContribution (![0, 4, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 24 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 608 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 24^2 = 608
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_20

theorem weighted_00_04_00_20 : b4RawGapContribution ![0, 4, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 20] = b4GapPatternWeight 4 0 20 * 0 :=
      b4GapContribution_from_row 0 4 0 20 0 row_00_04_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_20

theorem row_00_04_00_21 : b4RowContribution (![0, 4, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 25 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 657 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 25^2 = 657
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_21

theorem weighted_00_04_00_21 : b4RawGapContribution ![0, 4, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 21] = b4GapPatternWeight 4 0 21 * 0 :=
      b4GapContribution_from_row 0 4 0 21 0 row_00_04_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_21

theorem row_00_04_00_22 : b4RowContribution (![0, 4, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 26 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 708 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 26^2 = 708
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_22

theorem weighted_00_04_00_22 : b4RawGapContribution ![0, 4, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 22] = b4GapPatternWeight 4 0 22 * 0 :=
      b4GapContribution_from_row 0 4 0 22 0 row_00_04_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_22

theorem row_00_04_00_23 : b4RowContribution (![0, 4, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 27 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 761 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 27^2 = 761
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_23

theorem weighted_00_04_00_23 : b4RawGapContribution ![0, 4, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 23] = b4GapPatternWeight 4 0 23 * 0 :=
      b4GapContribution_from_row 0 4 0 23 0 row_00_04_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_23

theorem row_00_04_00_24 : b4RowContribution (![0, 4, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 28 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 816 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 28^2 = 816
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_24

theorem weighted_00_04_00_24 : b4RawGapContribution ![0, 4, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 24] = b4GapPatternWeight 4 0 24 * 0 :=
      b4GapContribution_from_row 0 4 0 24 0 row_00_04_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_24

theorem row_00_04_00_25 : b4RowContribution (![0, 4, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 4, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 4 + 29 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 873 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 4^2 + 29^2 = 873
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_00_25

theorem weighted_00_04_00_25 : b4RawGapContribution ![0, 4, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 0, 25] = b4GapPatternWeight 4 0 25 * 0 :=
      b4GapContribution_from_row 0 4 0 25 0 row_00_04_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_00_25

def dvalues_00_04_00 : Fin 26 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 300, 0, 588, 0, 564, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_00

theorem dblock_00_04_00 : b4GapPatternDBlock 0 4 0 = 1452 := by
  calc
    b4GapPatternDBlock 0 4 0 = ∑ d : Fin 26, dvalues_00_04_00 d := by
      apply b4GapDBlock_of_rows 0 4 0 dvalues_00_04_00
      intro d
      fin_cases d
      · exact weighted_00_04_00_00
      · exact weighted_00_04_00_01
      · exact weighted_00_04_00_02
      · exact weighted_00_04_00_03
      · exact weighted_00_04_00_04
      · exact weighted_00_04_00_05
      · exact weighted_00_04_00_06
      · exact weighted_00_04_00_07
      · exact weighted_00_04_00_08
      · exact weighted_00_04_00_09
      · exact weighted_00_04_00_10
      · exact weighted_00_04_00_11
      · exact weighted_00_04_00_12
      · exact weighted_00_04_00_13
      · exact weighted_00_04_00_14
      · exact weighted_00_04_00_15
      · exact weighted_00_04_00_16
      · exact weighted_00_04_00_17
      · exact weighted_00_04_00_18
      · exact weighted_00_04_00_19
      · exact weighted_00_04_00_20
      · exact weighted_00_04_00_21
      · exact weighted_00_04_00_22
      · exact weighted_00_04_00_23
      · exact weighted_00_04_00_24
      · exact weighted_00_04_00_25
    _ = 1452 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_00

end Paper7MomentGapNumeric
