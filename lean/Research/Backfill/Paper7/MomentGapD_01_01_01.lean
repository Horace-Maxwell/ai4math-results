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

theorem row_01_01_01_00 : b4RowContribution (![1, 2, 3, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 3] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 3 = 9
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 23 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 3^2 = 23
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_00

theorem weighted_01_01_01_00 : b4RawGapContribution ![1, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 1 1 1 0 0 row_01_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_00

theorem row_01_01_01_01 : b4RowContribution (![1, 2, 3, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 4] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 4 = 10
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 30 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 4^2 = 30
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_01

theorem weighted_01_01_01_01 : b4RawGapContribution ![1, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 1 1 1 1 0 row_01_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_01

def layers_01_01_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 20, 23, 23, 20, 15, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_01_01_02

theorem cells_01_01_01_02 : QTableValid (![1, 2, 3, 5] : Fin 4 → ℕ) layers_01_01_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_01_02

theorem valid_01_01_01_02 :
    SparseRowValid (![1, 2, 3, 5] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_01_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 3, 5] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 3 + 5 = 11
      decide
    have hzsq : (∑ i, (((![1, 2, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 39 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 3^2 + 5^2 = 39
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_01_02
#print axioms Paper7MomentGapNumeric.valid_01_01_01_02

def qvalues_01_01_01_02 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_01_02

theorem row_01_01_01_02 : b4RowContribution (![1, 2, 3, 5] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 2, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_01_01_02) :=
      sparseRow_sound (![1, 2, 3, 5] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_01_01_02) valid_01_01_01_02
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_01_02 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_01_02

theorem weighted_01_01_01_02 : b4RawGapContribution ![1, 1, 1, 2] = 576 := by
  calc
    b4RawGapContribution ![1, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 24 :=
      b4GapContribution_from_row 1 1 1 2 24 row_01_01_01_02
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_02

theorem row_01_01_01_03 : b4RowContribution (![1, 2, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 6] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 6 = 12
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 50 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 6^2 = 50
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_03

theorem weighted_01_01_01_03 : b4RawGapContribution ![1, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 1 1 1 3 0 row_01_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_03

theorem row_01_01_01_04 : b4RowContribution (![1, 2, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 7] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 7 = 13
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 63 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 7^2 = 63
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_04

theorem weighted_01_01_01_04 : b4RawGapContribution ![1, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 1 1 1 4 0 row_01_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_04

theorem row_01_01_01_05 : b4RowContribution (![1, 2, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 8] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 8 = 14
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 78 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 8^2 = 78
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_05

theorem weighted_01_01_01_05 : b4RawGapContribution ![1, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 1 1 1 5 0 row_01_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_05

theorem row_01_01_01_06 : b4RowContribution (![1, 2, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 9] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 9 = 15
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 95 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 9^2 = 95
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_06

theorem weighted_01_01_01_06 : b4RawGapContribution ![1, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 1 1 1 6 0 row_01_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_06

theorem row_01_01_01_07 : b4RowContribution (![1, 2, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 10] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 10 = 16
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 10^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_07

theorem weighted_01_01_01_07 : b4RawGapContribution ![1, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 1 1 1 7 0 row_01_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_07

theorem row_01_01_01_08 : b4RowContribution (![1, 2, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 11] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 11 = 17
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 135 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 11^2 = 135
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_08

theorem weighted_01_01_01_08 : b4RawGapContribution ![1, 1, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 0 :=
      b4GapContribution_from_row 1 1 1 8 0 row_01_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_08

theorem row_01_01_01_09 : b4RowContribution (![1, 2, 3, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 12] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 12 = 18
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 158 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 12^2 = 158
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_09

theorem weighted_01_01_01_09 : b4RawGapContribution ![1, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 1 1 1 9 0 row_01_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_09

def layers_01_01_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 23, 20, 15, 9, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_01_01_10

theorem cells_01_01_01_10 : QTableValid (![1, 2, 3, 13] : Fin 4 → ℕ) layers_01_01_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_01_10

theorem valid_01_01_01_10 :
    SparseRowValid (![1, 2, 3, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_01_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 3, 13] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 3 + 13 = 19
      decide
    have hzsq : (∑ i, (((![1, 2, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 3^2 + 13^2 = 183
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_01_10
#print axioms Paper7MomentGapNumeric.valid_01_01_01_10

def qvalues_01_01_01_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_01_10

theorem row_01_01_01_10 : b4RowContribution (![1, 2, 3, 13] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 2, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_01_01_01_10) :=
      sparseRow_sound (![1, 2, 3, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_01_01_10) valid_01_01_01_10
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_01_10 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_01_10

theorem weighted_01_01_01_10 : b4RawGapContribution ![1, 1, 1, 10] = 576 := by
  calc
    b4RawGapContribution ![1, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 24 :=
      b4GapContribution_from_row 1 1 1 10 24 row_01_01_01_10
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_10

def layers_01_01_01_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 23, 20, 15, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_01_01_11

theorem cells_01_01_01_11 : QTableValid (![1, 2, 3, 14] : Fin 4 → ℕ) layers_01_01_01_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_01_11

theorem valid_01_01_01_11 :
    SparseRowValid (![1, 2, 3, 14] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_01_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 3, 14] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 3 + 14 = 20
      decide
    have hzsq : (∑ i, (((![1, 2, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 3^2 + 14^2 = 210
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_01_11
#print axioms Paper7MomentGapNumeric.valid_01_01_01_11

def qvalues_01_01_01_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_01_11

theorem row_01_01_01_11 : b4RowContribution (![1, 2, 3, 14] : Fin 4 → ℕ) = 23 := by
  calc
    b4RowContribution (![1, 2, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_01_01_01_11) :=
      sparseRow_sound (![1, 2, 3, 14] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_01_11) valid_01_01_01_11
    _ = 23 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_01_11 Q := by
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
        _ = 23 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_01_11

theorem weighted_01_01_01_11 : b4RawGapContribution ![1, 1, 1, 11] = 552 := by
  calc
    b4RawGapContribution ![1, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 23 :=
      b4GapContribution_from_row 1 1 1 11 23 row_01_01_01_11
    _ = 552 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_11

def layers_01_01_01_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 23, 20, 15]]
#print axioms Paper7MomentGapNumeric.layers_01_01_01_12

theorem cells_01_01_01_12 : QTableValid (![1, 2, 3, 15] : Fin 4 → ℕ) layers_01_01_01_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_01_12

theorem valid_01_01_01_12 :
    SparseRowValid (![1, 2, 3, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_01_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 3, 15] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 3 + 15 = 21
      decide
    have hzsq : (∑ i, (((![1, 2, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 239 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 3^2 + 15^2 = 239
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_01_12
#print axioms Paper7MomentGapNumeric.valid_01_01_01_12

def qvalues_01_01_01_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_01_12

theorem row_01_01_01_12 : b4RowContribution (![1, 2, 3, 15] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![1, 2, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_01_12) :=
      sparseRow_sound (![1, 2, 3, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_01_12) valid_01_01_01_12
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_01_12 Q := by
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
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_01_12

theorem weighted_01_01_01_12 : b4RawGapContribution ![1, 1, 1, 12] = 1128 := by
  calc
    b4RawGapContribution ![1, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 47 :=
      b4GapContribution_from_row 1 1 1 12 47 row_01_01_01_12
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_12

theorem row_01_01_01_13 : b4RowContribution (![1, 2, 3, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 16] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 16 = 22
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 16^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_13

theorem weighted_01_01_01_13 : b4RawGapContribution ![1, 1, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 13] = b4GapPatternWeight 1 1 13 * 0 :=
      b4GapContribution_from_row 1 1 1 13 0 row_01_01_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_13

theorem row_01_01_01_14 : b4RowContribution (![1, 2, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 17] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 17 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 17^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_14

theorem weighted_01_01_01_14 : b4RawGapContribution ![1, 1, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 14] = b4GapPatternWeight 1 1 14 * 0 :=
      b4GapContribution_from_row 1 1 1 14 0 row_01_01_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_14

theorem row_01_01_01_15 : b4RowContribution (![1, 2, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 18] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 18 = 24
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 18^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_15

theorem weighted_01_01_01_15 : b4RawGapContribution ![1, 1, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 15] = b4GapPatternWeight 1 1 15 * 0 :=
      b4GapContribution_from_row 1 1 1 15 0 row_01_01_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_15

theorem row_01_01_01_16 : b4RowContribution (![1, 2, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 19] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 19 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 19^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_16

theorem weighted_01_01_01_16 : b4RawGapContribution ![1, 1, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 16] = b4GapPatternWeight 1 1 16 * 0 :=
      b4GapContribution_from_row 1 1 1 16 0 row_01_01_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_16

theorem row_01_01_01_17 : b4RowContribution (![1, 2, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 20] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 20 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 20^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_17

theorem weighted_01_01_01_17 : b4RawGapContribution ![1, 1, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 17] = b4GapPatternWeight 1 1 17 * 0 :=
      b4GapContribution_from_row 1 1 1 17 0 row_01_01_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_17

theorem row_01_01_01_18 : b4RowContribution (![1, 2, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 21] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 21 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 21^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_18

theorem weighted_01_01_01_18 : b4RawGapContribution ![1, 1, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 18] = b4GapPatternWeight 1 1 18 * 0 :=
      b4GapContribution_from_row 1 1 1 18 0 row_01_01_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_18

theorem row_01_01_01_19 : b4RowContribution (![1, 2, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 22] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 22 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 22^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_19

theorem weighted_01_01_01_19 : b4RawGapContribution ![1, 1, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 19] = b4GapPatternWeight 1 1 19 * 0 :=
      b4GapContribution_from_row 1 1 1 19 0 row_01_01_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_19

theorem row_01_01_01_20 : b4RowContribution (![1, 2, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 23] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 23 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 543 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 23^2 = 543
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_20

theorem weighted_01_01_01_20 : b4RawGapContribution ![1, 1, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 20] = b4GapPatternWeight 1 1 20 * 0 :=
      b4GapContribution_from_row 1 1 1 20 0 row_01_01_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_20

theorem row_01_01_01_21 : b4RowContribution (![1, 2, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 24] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 24 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 590 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 24^2 = 590
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_21

theorem weighted_01_01_01_21 : b4RawGapContribution ![1, 1, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 21] = b4GapPatternWeight 1 1 21 * 0 :=
      b4GapContribution_from_row 1 1 1 21 0 row_01_01_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_21

theorem row_01_01_01_22 : b4RowContribution (![1, 2, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 25] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 25 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 639 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 25^2 = 639
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_22

theorem weighted_01_01_01_22 : b4RawGapContribution ![1, 1, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 22] = b4GapPatternWeight 1 1 22 * 0 :=
      b4GapContribution_from_row 1 1 1 22 0 row_01_01_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_22

theorem row_01_01_01_23 : b4RowContribution (![1, 2, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 26] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 26 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 690 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 26^2 = 690
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_23

theorem weighted_01_01_01_23 : b4RawGapContribution ![1, 1, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 23] = b4GapPatternWeight 1 1 23 * 0 :=
      b4GapContribution_from_row 1 1 1 23 0 row_01_01_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_23

theorem row_01_01_01_24 : b4RowContribution (![1, 2, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 27] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 27 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 743 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 27^2 = 743
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_24

theorem weighted_01_01_01_24 : b4RawGapContribution ![1, 1, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 24] = b4GapPatternWeight 1 1 24 * 0 :=
      b4GapContribution_from_row 1 1 1 24 0 row_01_01_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_24

theorem row_01_01_01_25 : b4RowContribution (![1, 2, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 28] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 28 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 798 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 28^2 = 798
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_25

theorem weighted_01_01_01_25 : b4RawGapContribution ![1, 1, 1, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 25] = b4GapPatternWeight 1 1 25 * 0 :=
      b4GapContribution_from_row 1 1 1 25 0 row_01_01_01_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_25

theorem row_01_01_01_26 : b4RowContribution (![1, 2, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 29] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 29 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 855 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 29^2 = 855
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_26

theorem weighted_01_01_01_26 : b4RawGapContribution ![1, 1, 1, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 26] = b4GapPatternWeight 1 1 26 * 0 :=
      b4GapContribution_from_row 1 1 1 26 0 row_01_01_01_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_26

theorem row_01_01_01_27 : b4RowContribution (![1, 2, 3, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 30] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 30 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 914 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 30^2 = 914
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_27

theorem weighted_01_01_01_27 : b4RawGapContribution ![1, 1, 1, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 27] = b4GapPatternWeight 1 1 27 * 0 :=
      b4GapContribution_from_row 1 1 1 27 0 row_01_01_01_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_27

theorem row_01_01_01_28 : b4RowContribution (![1, 2, 3, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 3, 31] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 3 + 31 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 3, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 975 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 3^2 + 31^2 = 975
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_01_28

theorem weighted_01_01_01_28 : b4RawGapContribution ![1, 1, 1, 28] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 1, 28] = b4GapPatternWeight 1 1 28 * 0 :=
      b4GapContribution_from_row 1 1 1 28 0 row_01_01_01_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_01_28

def dvalues_01_01_01 : Fin 29 → ℕ := ![0, 0, 576, 0, 0, 0, 0, 0, 0, 0, 576, 552, 1128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_01

theorem dblock_01_01_01 : b4GapPatternDBlock 1 1 1 = 2832 := by
  calc
    b4GapPatternDBlock 1 1 1 = ∑ d : Fin 29, dvalues_01_01_01 d := by
      apply b4GapDBlock_of_rows 1 1 1 dvalues_01_01_01
      intro d
      fin_cases d
      · exact weighted_01_01_01_00
      · exact weighted_01_01_01_01
      · exact weighted_01_01_01_02
      · exact weighted_01_01_01_03
      · exact weighted_01_01_01_04
      · exact weighted_01_01_01_05
      · exact weighted_01_01_01_06
      · exact weighted_01_01_01_07
      · exact weighted_01_01_01_08
      · exact weighted_01_01_01_09
      · exact weighted_01_01_01_10
      · exact weighted_01_01_01_11
      · exact weighted_01_01_01_12
      · exact weighted_01_01_01_13
      · exact weighted_01_01_01_14
      · exact weighted_01_01_01_15
      · exact weighted_01_01_01_16
      · exact weighted_01_01_01_17
      · exact weighted_01_01_01_18
      · exact weighted_01_01_01_19
      · exact weighted_01_01_01_20
      · exact weighted_01_01_01_21
      · exact weighted_01_01_01_22
      · exact weighted_01_01_01_23
      · exact weighted_01_01_01_24
      · exact weighted_01_01_01_25
      · exact weighted_01_01_01_26
      · exact weighted_01_01_01_27
      · exact weighted_01_01_01_28
    _ = 2832 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_01

end Paper7MomentGapNumeric
