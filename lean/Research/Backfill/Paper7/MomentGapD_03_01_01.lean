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

theorem row_03_01_01_00 : b4RowContribution (![3, 4, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 5] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 5 = 17
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 75 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 5^2 = 75
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_00

theorem weighted_03_01_01_00 : b4RawGapContribution ![3, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 3 1 1 0 0 row_03_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_00

theorem row_03_01_01_01 : b4RowContribution (![3, 4, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 6] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 6 = 18
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 86 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 6^2 = 86
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_01

theorem weighted_03_01_01_01 : b4RawGapContribution ![3, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 3 1 1 1 0 row_03_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_01

theorem row_03_01_01_02 : b4RowContribution (![3, 4, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 7] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 7 = 19
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 7^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_02

theorem weighted_03_01_01_02 : b4RawGapContribution ![3, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 3 1 1 2 0 row_03_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_02

theorem row_03_01_01_03 : b4RowContribution (![3, 4, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 8 = 20
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 8^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_03

theorem weighted_03_01_01_03 : b4RawGapContribution ![3, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 3 1 1 3 0 row_03_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_03

theorem row_03_01_01_04 : b4RowContribution (![3, 4, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 9 = 21
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 131 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 9^2 = 131
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_04

theorem weighted_03_01_01_04 : b4RawGapContribution ![3, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 3 1 1 4 0 row_03_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_04

theorem row_03_01_01_05 : b4RowContribution (![3, 4, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 10 = 22
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 10^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_05

theorem weighted_03_01_01_05 : b4RawGapContribution ![3, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 3 1 1 5 0 row_03_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_05

theorem row_03_01_01_06 : b4RowContribution (![3, 4, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 11 = 23
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 11^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_06

theorem weighted_03_01_01_06 : b4RawGapContribution ![3, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 3 1 1 6 0 row_03_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_06

theorem row_03_01_01_07 : b4RowContribution (![3, 4, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 12 = 24
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 12^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_07

theorem weighted_03_01_01_07 : b4RawGapContribution ![3, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 3 1 1 7 0 row_03_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_07

def layers_03_01_01_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 18, 17, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 69, 86, 100, 110, 116, 119, 120, 120, 119, 116, 110, 100, 86]]
#print axioms Paper7MomentGapNumeric.layers_03_01_01_08

theorem cells_03_01_01_08 : QTableValid (![3, 4, 5, 13] : Fin 4 → ℕ) layers_03_01_01_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_01_08

theorem valid_03_01_01_08 :
    SparseRowValid (![3, 4, 5, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_01_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 5, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 5 + 13 = 25
      decide
    have hzsq : (∑ i, (((![3, 4, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 5^2 + 13^2 = 219
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_01_08
#print axioms Paper7MomentGapNumeric.valid_03_01_01_08

def qvalues_03_01_01_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_01_08

theorem row_03_01_01_08 : b4RowContribution (![3, 4, 5, 13] : Fin 4 → ℕ) = 110 := by
  calc
    b4RowContribution (![3, 4, 5, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_03_01_01_08) :=
      sparseRow_sound (![3, 4, 5, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_01_08) valid_03_01_01_08
    _ = 110 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_01_08 Q := by
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
        _ = 110 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_01_08

theorem weighted_03_01_01_08 : b4RawGapContribution ![3, 1, 1, 8] = 2640 := by
  calc
    b4RawGapContribution ![3, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 110 :=
      b4GapContribution_from_row 3 1 1 8 110 row_03_01_01_08
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_08

theorem row_03_01_01_09 : b4RowContribution (![3, 4, 5, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 14 = 26
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 14^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_09

theorem weighted_03_01_01_09 : b4RawGapContribution ![3, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 3 1 1 9 0 row_03_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_09

def layers_03_01_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 18, 17, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 69, 86, 100, 110, 116, 119, 120, 120, 120, 120, 119, 116, 110]]
#print axioms Paper7MomentGapNumeric.layers_03_01_01_10

theorem cells_03_01_01_10 : QTableValid (![3, 4, 5, 15] : Fin 4 → ℕ) layers_03_01_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_01_10

theorem valid_03_01_01_10 :
    SparseRowValid (![3, 4, 5, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 5, 15] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 5 + 15 = 27
      decide
    have hzsq : (∑ i, (((![3, 4, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 5^2 + 15^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_01_10
#print axioms Paper7MomentGapNumeric.valid_03_01_01_10

def qvalues_03_01_01_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_01_10

theorem row_03_01_01_10 : b4RowContribution (![3, 4, 5, 15] : Fin 4 → ℕ) = 100 := by
  calc
    b4RowContribution (![3, 4, 5, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_01_01_10) :=
      sparseRow_sound (![3, 4, 5, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_01_10) valid_03_01_01_10
    _ = 100 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_01_10 Q := by
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
        _ = 100 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_01_10

theorem weighted_03_01_01_10 : b4RawGapContribution ![3, 1, 1, 10] = 2400 := by
  calc
    b4RawGapContribution ![3, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 100 :=
      b4GapContribution_from_row 3 1 1 10 100 row_03_01_01_10
    _ = 2400 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_10

theorem row_03_01_01_11 : b4RowContribution (![3, 4, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 16 = 28
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 16^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_11

theorem weighted_03_01_01_11 : b4RawGapContribution ![3, 1, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 0 :=
      b4GapContribution_from_row 3 1 1 11 0 row_03_01_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_11

theorem row_03_01_01_12 : b4RowContribution (![3, 4, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 17 = 29
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 17^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_12

theorem weighted_03_01_01_12 : b4RawGapContribution ![3, 1, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 0 :=
      b4GapContribution_from_row 3 1 1 12 0 row_03_01_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_12

theorem row_03_01_01_13 : b4RowContribution (![3, 4, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 18 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 18^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_13

theorem weighted_03_01_01_13 : b4RawGapContribution ![3, 1, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 13] = b4GapPatternWeight 1 1 13 * 0 :=
      b4GapContribution_from_row 3 1 1 13 0 row_03_01_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_13

theorem row_03_01_01_14 : b4RowContribution (![3, 4, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 19 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 19^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_14

theorem weighted_03_01_01_14 : b4RawGapContribution ![3, 1, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 14] = b4GapPatternWeight 1 1 14 * 0 :=
      b4GapContribution_from_row 3 1 1 14 0 row_03_01_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_14

theorem row_03_01_01_15 : b4RowContribution (![3, 4, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 20 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 20^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_15

theorem weighted_03_01_01_15 : b4RawGapContribution ![3, 1, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 15] = b4GapPatternWeight 1 1 15 * 0 :=
      b4GapContribution_from_row 3 1 1 15 0 row_03_01_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_15

theorem row_03_01_01_16 : b4RowContribution (![3, 4, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 21 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 21^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_16

theorem weighted_03_01_01_16 : b4RawGapContribution ![3, 1, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 16] = b4GapPatternWeight 1 1 16 * 0 :=
      b4GapContribution_from_row 3 1 1 16 0 row_03_01_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_16

theorem row_03_01_01_17 : b4RowContribution (![3, 4, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 22 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 22^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_17

theorem weighted_03_01_01_17 : b4RawGapContribution ![3, 1, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 17] = b4GapPatternWeight 1 1 17 * 0 :=
      b4GapContribution_from_row 3 1 1 17 0 row_03_01_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_17

theorem row_03_01_01_18 : b4RowContribution (![3, 4, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 23 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 23^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_18

theorem weighted_03_01_01_18 : b4RawGapContribution ![3, 1, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 18] = b4GapPatternWeight 1 1 18 * 0 :=
      b4GapContribution_from_row 3 1 1 18 0 row_03_01_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_18

theorem row_03_01_01_19 : b4RowContribution (![3, 4, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 24 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 24^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_19

theorem weighted_03_01_01_19 : b4RawGapContribution ![3, 1, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 19] = b4GapPatternWeight 1 1 19 * 0 :=
      b4GapContribution_from_row 3 1 1 19 0 row_03_01_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_19

theorem row_03_01_01_20 : b4RowContribution (![3, 4, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 5, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 5 + 25 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 675 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 5^2 + 25^2 = 675
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_01_20

theorem weighted_03_01_01_20 : b4RawGapContribution ![3, 1, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 1, 20] = b4GapPatternWeight 1 1 20 * 0 :=
      b4GapContribution_from_row 3 1 1 20 0 row_03_01_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_01_20

def dvalues_03_01_01 : Fin 21 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 2640, 0, 2400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_01

theorem dblock_03_01_01 : b4GapPatternDBlock 3 1 1 = 5040 := by
  calc
    b4GapPatternDBlock 3 1 1 = ∑ d : Fin 21, dvalues_03_01_01 d := by
      apply b4GapDBlock_of_rows 3 1 1 dvalues_03_01_01
      intro d
      fin_cases d
      · exact weighted_03_01_01_00
      · exact weighted_03_01_01_01
      · exact weighted_03_01_01_02
      · exact weighted_03_01_01_03
      · exact weighted_03_01_01_04
      · exact weighted_03_01_01_05
      · exact weighted_03_01_01_06
      · exact weighted_03_01_01_07
      · exact weighted_03_01_01_08
      · exact weighted_03_01_01_09
      · exact weighted_03_01_01_10
      · exact weighted_03_01_01_11
      · exact weighted_03_01_01_12
      · exact weighted_03_01_01_13
      · exact weighted_03_01_01_14
      · exact weighted_03_01_01_15
      · exact weighted_03_01_01_16
      · exact weighted_03_01_01_17
      · exact weighted_03_01_01_18
      · exact weighted_03_01_01_19
      · exact weighted_03_01_01_20
    _ = 5040 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_01

end Paper7MomentGapNumeric
