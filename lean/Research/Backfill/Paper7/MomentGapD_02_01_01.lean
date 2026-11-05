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

def layers_02_01_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 40, 46, 46, 40, 30, 19, 10, 4, 1, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_01_01_00

theorem cells_02_01_01_00 : QTableValid (![2, 3, 4, 4] : Fin 4 → ℕ) layers_02_01_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_01_00

theorem valid_02_01_01_00 :
    SparseRowValid (![2, 3, 4, 4] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_02_01_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 4, 4] : Fin 4 → ℕ) i) = 13 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 4 + 4 = 13
      decide
    have hzsq : (∑ i, (((![2, 3, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 45 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 4^2 + 4^2 = 45
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_01_00
#print axioms Paper7MomentGapNumeric.valid_02_01_01_00

def qvalues_02_01_01_00 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_01_00

theorem row_02_01_01_00 : b4RowContribution (![2, 3, 4, 4] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![2, 3, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_02_01_01_00) :=
      sparseRow_sound (![2, 3, 4, 4] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_02_01_01_00) valid_02_01_01_00
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_01_00 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_01_00

theorem weighted_02_01_01_00 : b4RawGapContribution ![2, 1, 1, 0] = 12 := by
  calc
    b4RawGapContribution ![2, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 1 :=
      b4GapContribution_from_row 2 1 1 0 1 row_02_01_01_00
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_00

theorem row_02_01_01_01 : b4RowContribution (![2, 3, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 5] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 5 = 14
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 54 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 5^2 = 54
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_01

theorem weighted_02_01_01_01 : b4RawGapContribution ![2, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 2 1 1 1 0 row_02_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_01

theorem row_02_01_01_02 : b4RowContribution (![2, 3, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 6 = 15
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 65 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 6^2 = 65
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_02

theorem weighted_02_01_01_02 : b4RawGapContribution ![2, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 2 1 1 2 0 row_02_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_02

theorem row_02_01_01_03 : b4RowContribution (![2, 3, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 7 = 16
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 78 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 7^2 = 78
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_03

theorem weighted_02_01_01_03 : b4RawGapContribution ![2, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 2 1 1 3 0 row_02_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_03

theorem row_02_01_01_04 : b4RowContribution (![2, 3, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 8 = 17
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 93 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 8^2 = 93
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_04

theorem weighted_02_01_01_04 : b4RawGapContribution ![2, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 2 1 1 4 0 row_02_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_04

theorem row_02_01_01_05 : b4RowContribution (![2, 3, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 9 = 18
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 110 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 9^2 = 110
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_05

theorem weighted_02_01_01_05 : b4RawGapContribution ![2, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 2 1 1 5 0 row_02_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_05

theorem row_02_01_01_06 : b4RowContribution (![2, 3, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 10 = 19
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 10^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_06

theorem weighted_02_01_01_06 : b4RawGapContribution ![2, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 2 1 1 6 0 row_02_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_06

theorem row_02_01_01_07 : b4RowContribution (![2, 3, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 11] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 11 = 20
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 11^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_07

theorem weighted_02_01_01_07 : b4RawGapContribution ![2, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 2 1 1 7 0 row_02_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_07

theorem row_02_01_01_08 : b4RowContribution (![2, 3, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 12 = 21
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 173 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 12^2 = 173
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_08

theorem weighted_02_01_01_08 : b4RawGapContribution ![2, 1, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 0 :=
      b4GapContribution_from_row 2 1 1 8 0 row_02_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_08

theorem row_02_01_01_09 : b4RowContribution (![2, 3, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 13 = 22
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 13^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_09

theorem weighted_02_01_01_09 : b4RawGapContribution ![2, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 2 1 1 9 0 row_02_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_09

def layers_02_01_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 41, 50, 56, 59, 60, 60, 60, 60, 60, 60, 59, 56, 50, 41]]
#print axioms Paper7MomentGapNumeric.layers_02_01_01_10

theorem cells_02_01_01_10 : QTableValid (![2, 3, 4, 14] : Fin 4 → ℕ) layers_02_01_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_01_10

theorem valid_02_01_01_10 :
    SparseRowValid (![2, 3, 4, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_01_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 4, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 4 + 14 = 23
      decide
    have hzsq : (∑ i, (((![2, 3, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 4^2 + 14^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_01_10
#print axioms Paper7MomentGapNumeric.valid_02_01_01_10

def qvalues_02_01_01_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_01_10

theorem row_02_01_01_10 : b4RowContribution (![2, 3, 4, 14] : Fin 4 → ℕ) = 60 := by
  calc
    b4RowContribution (![2, 3, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_01_01_10) :=
      sparseRow_sound (![2, 3, 4, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_01_01_10) valid_02_01_01_10
    _ = 60 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_01_10 Q := by
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
        _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_01_10

theorem weighted_02_01_01_10 : b4RawGapContribution ![2, 1, 1, 10] = 1440 := by
  calc
    b4RawGapContribution ![2, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 60 :=
      b4GapContribution_from_row 2 1 1 10 60 row_02_01_01_10
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_10

theorem row_02_01_01_11 : b4RowContribution (![2, 3, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 15 = 24
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 15^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_11

theorem weighted_02_01_01_11 : b4RawGapContribution ![2, 1, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 0 :=
      b4GapContribution_from_row 2 1 1 11 0 row_02_01_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_11

def layers_02_01_01_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 41, 50, 56, 59, 60, 60, 60, 60, 60, 60, 60, 60, 59, 56]]
#print axioms Paper7MomentGapNumeric.layers_02_01_01_12

theorem cells_02_01_01_12 : QTableValid (![2, 3, 4, 16] : Fin 4 → ℕ) layers_02_01_01_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_01_12

theorem valid_02_01_01_12 :
    SparseRowValid (![2, 3, 4, 16] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_02_01_01_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 4, 16] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 4 + 16 = 25
      decide
    have hzsq : (∑ i, (((![2, 3, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 4^2 + 16^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_01_12
#print axioms Paper7MomentGapNumeric.valid_02_01_01_12

def qvalues_02_01_01_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_01_12

theorem row_02_01_01_12 : b4RowContribution (![2, 3, 4, 16] : Fin 4 → ℕ) = 110 := by
  calc
    b4RowContribution (![2, 3, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_02_01_01_12) :=
      sparseRow_sound (![2, 3, 4, 16] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_02_01_01_12) valid_02_01_01_12
    _ = 110 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_01_12 Q := by
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
        _ = 110 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_01_12

theorem weighted_02_01_01_12 : b4RawGapContribution ![2, 1, 1, 12] = 2640 := by
  calc
    b4RawGapContribution ![2, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 110 :=
      b4GapContribution_from_row 2 1 1 12 110 row_02_01_01_12
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_12

theorem row_02_01_01_13 : b4RowContribution (![2, 3, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 17 = 26
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 17^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_13

theorem weighted_02_01_01_13 : b4RawGapContribution ![2, 1, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 13] = b4GapPatternWeight 1 1 13 * 0 :=
      b4GapContribution_from_row 2 1 1 13 0 row_02_01_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_13

theorem row_02_01_01_14 : b4RowContribution (![2, 3, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 18 = 27
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 18^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_14

theorem weighted_02_01_01_14 : b4RawGapContribution ![2, 1, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 14] = b4GapPatternWeight 1 1 14 * 0 :=
      b4GapContribution_from_row 2 1 1 14 0 row_02_01_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_14

theorem row_02_01_01_15 : b4RowContribution (![2, 3, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 19 = 28
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 19^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_15

theorem weighted_02_01_01_15 : b4RawGapContribution ![2, 1, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 15] = b4GapPatternWeight 1 1 15 * 0 :=
      b4GapContribution_from_row 2 1 1 15 0 row_02_01_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_15

theorem row_02_01_01_16 : b4RowContribution (![2, 3, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 20 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 20^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_16

theorem weighted_02_01_01_16 : b4RawGapContribution ![2, 1, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 16] = b4GapPatternWeight 1 1 16 * 0 :=
      b4GapContribution_from_row 2 1 1 16 0 row_02_01_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_16

theorem row_02_01_01_17 : b4RowContribution (![2, 3, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 21 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 21^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_17

theorem weighted_02_01_01_17 : b4RawGapContribution ![2, 1, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 17] = b4GapPatternWeight 1 1 17 * 0 :=
      b4GapContribution_from_row 2 1 1 17 0 row_02_01_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_17

theorem row_02_01_01_18 : b4RowContribution (![2, 3, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 22 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 22^2 = 513
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_18

theorem weighted_02_01_01_18 : b4RawGapContribution ![2, 1, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 18] = b4GapPatternWeight 1 1 18 * 0 :=
      b4GapContribution_from_row 2 1 1 18 0 row_02_01_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_18

theorem row_02_01_01_19 : b4RowContribution (![2, 3, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 23 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 23^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_19

theorem weighted_02_01_01_19 : b4RawGapContribution ![2, 1, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 19] = b4GapPatternWeight 1 1 19 * 0 :=
      b4GapContribution_from_row 2 1 1 19 0 row_02_01_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_19

theorem row_02_01_01_20 : b4RowContribution (![2, 3, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 24 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 605 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 24^2 = 605
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_20

theorem weighted_02_01_01_20 : b4RawGapContribution ![2, 1, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 20] = b4GapPatternWeight 1 1 20 * 0 :=
      b4GapContribution_from_row 2 1 1 20 0 row_02_01_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_20

theorem row_02_01_01_21 : b4RowContribution (![2, 3, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 25 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 654 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 25^2 = 654
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_21

theorem weighted_02_01_01_21 : b4RawGapContribution ![2, 1, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 21] = b4GapPatternWeight 1 1 21 * 0 :=
      b4GapContribution_from_row 2 1 1 21 0 row_02_01_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_21

theorem row_02_01_01_22 : b4RowContribution (![2, 3, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 26 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 705 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 26^2 = 705
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_22

theorem weighted_02_01_01_22 : b4RawGapContribution ![2, 1, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 22] = b4GapPatternWeight 1 1 22 * 0 :=
      b4GapContribution_from_row 2 1 1 22 0 row_02_01_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_22

theorem row_02_01_01_23 : b4RowContribution (![2, 3, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 27 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 758 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 27^2 = 758
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_23

theorem weighted_02_01_01_23 : b4RawGapContribution ![2, 1, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 23] = b4GapPatternWeight 1 1 23 * 0 :=
      b4GapContribution_from_row 2 1 1 23 0 row_02_01_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_23

theorem row_02_01_01_24 : b4RowContribution (![2, 3, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 4, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 4 + 28 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 813 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 4^2 + 28^2 = 813
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_01_24

theorem weighted_02_01_01_24 : b4RawGapContribution ![2, 1, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 1, 24] = b4GapPatternWeight 1 1 24 * 0 :=
      b4GapContribution_from_row 2 1 1 24 0 row_02_01_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_01_24

def dvalues_02_01_01 : Fin 25 → ℕ := ![12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1440, 0, 2640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_01

theorem dblock_02_01_01 : b4GapPatternDBlock 2 1 1 = 4092 := by
  calc
    b4GapPatternDBlock 2 1 1 = ∑ d : Fin 25, dvalues_02_01_01 d := by
      apply b4GapDBlock_of_rows 2 1 1 dvalues_02_01_01
      intro d
      fin_cases d
      · exact weighted_02_01_01_00
      · exact weighted_02_01_01_01
      · exact weighted_02_01_01_02
      · exact weighted_02_01_01_03
      · exact weighted_02_01_01_04
      · exact weighted_02_01_01_05
      · exact weighted_02_01_01_06
      · exact weighted_02_01_01_07
      · exact weighted_02_01_01_08
      · exact weighted_02_01_01_09
      · exact weighted_02_01_01_10
      · exact weighted_02_01_01_11
      · exact weighted_02_01_01_12
      · exact weighted_02_01_01_13
      · exact weighted_02_01_01_14
      · exact weighted_02_01_01_15
      · exact weighted_02_01_01_16
      · exact weighted_02_01_01_17
      · exact weighted_02_01_01_18
      · exact weighted_02_01_01_19
      · exact weighted_02_01_01_20
      · exact weighted_02_01_01_21
      · exact weighted_02_01_01_22
      · exact weighted_02_01_01_23
      · exact weighted_02_01_01_24
    _ = 4092 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_01

end Paper7MomentGapNumeric
