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

theorem row_02_00_03_00 : b4RowContribution (![2, 2, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 5] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 5 = 14
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 5^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_00

theorem weighted_02_00_03_00 : b4RawGapContribution ![2, 0, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 0] = b4GapPatternWeight 0 3 0 * 0 :=
      b4GapContribution_from_row 2 0 3 0 0 row_02_00_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_00

theorem row_02_00_03_01 : b4RowContribution (![2, 2, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 6 = 15
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 69 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 6^2 = 69
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_01

theorem weighted_02_00_03_01 : b4RawGapContribution ![2, 0, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 1] = b4GapPatternWeight 0 3 1 * 0 :=
      b4GapContribution_from_row 2 0 3 1 0 row_02_00_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_01

theorem row_02_00_03_02 : b4RowContribution (![2, 2, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 7 = 16
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 7^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_02

theorem weighted_02_00_03_02 : b4RawGapContribution ![2, 0, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 2] = b4GapPatternWeight 0 3 2 * 0 :=
      b4GapContribution_from_row 2 0 3 2 0 row_02_00_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_02

theorem row_02_00_03_03 : b4RowContribution (![2, 2, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 8 = 17
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 97 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 8^2 = 97
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_03

theorem weighted_02_00_03_03 : b4RawGapContribution ![2, 0, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 3] = b4GapPatternWeight 0 3 3 * 0 :=
      b4GapContribution_from_row 2 0 3 3 0 row_02_00_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_03

theorem row_02_00_03_04 : b4RowContribution (![2, 2, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 9 = 18
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 9^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_04

theorem weighted_02_00_03_04 : b4RawGapContribution ![2, 0, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 4] = b4GapPatternWeight 0 3 4 * 0 :=
      b4GapContribution_from_row 2 0 3 4 0 row_02_00_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_04

theorem row_02_00_03_05 : b4RowContribution (![2, 2, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 10 = 19
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 133 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 10^2 = 133
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_05

theorem weighted_02_00_03_05 : b4RawGapContribution ![2, 0, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 5] = b4GapPatternWeight 0 3 5 * 0 :=
      b4GapContribution_from_row 2 0 3 5 0 row_02_00_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_05

theorem row_02_00_03_06 : b4RowContribution (![2, 2, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 11] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 11 = 20
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 154 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 11^2 = 154
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_06

theorem weighted_02_00_03_06 : b4RawGapContribution ![2, 0, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 6] = b4GapPatternWeight 0 3 6 * 0 :=
      b4GapContribution_from_row 2 0 3 6 0 row_02_00_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_06

theorem row_02_00_03_07 : b4RowContribution (![2, 2, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 12 = 21
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 12^2 = 177
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_07

theorem weighted_02_00_03_07 : b4RawGapContribution ![2, 0, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 7] = b4GapPatternWeight 0 3 7 * 0 :=
      b4GapContribution_from_row 2 0 3 7 0 row_02_00_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_07

theorem row_02_00_03_08 : b4RowContribution (![2, 2, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 13 = 22
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 13^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_08

theorem weighted_02_00_03_08 : b4RawGapContribution ![2, 0, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 8] = b4GapPatternWeight 0 3 8 * 0 :=
      b4GapContribution_from_row 2 0 3 8 0 row_02_00_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_08

def layers_02_00_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 44, 50, 53, 54, 54, 54, 54, 54, 54, 53, 50, 44, 36]]
#print axioms Paper7MomentGapNumeric.layers_02_00_03_09

theorem cells_02_00_03_09 : QTableValid (![2, 2, 5, 14] : Fin 4 → ℕ) layers_02_00_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_03_09

theorem valid_02_00_03_09 :
    SparseRowValid (![2, 2, 5, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 5, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 5 + 14 = 23
      decide
    have hzsq : (∑ i, (((![2, 2, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 5^2 + 14^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_03_09
#print axioms Paper7MomentGapNumeric.valid_02_00_03_09

def qvalues_02_00_03_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_03_09

theorem row_02_00_03_09 : b4RowContribution (![2, 2, 5, 14] : Fin 4 → ℕ) = 104 := by
  calc
    b4RowContribution (![2, 2, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_03_09) :=
      sparseRow_sound (![2, 2, 5, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_02_00_03_09) valid_02_00_03_09
    _ = 104 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_03_09 Q := by
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
        _ = 104 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_03_09

theorem weighted_02_00_03_09 : b4RawGapContribution ![2, 0, 3, 9] = 1248 := by
  calc
    b4RawGapContribution ![2, 0, 3, 9] = b4GapPatternWeight 0 3 9 * 104 :=
      b4GapContribution_from_row 2 0 3 9 104 row_02_00_03_09
    _ = 1248 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_09

theorem row_02_00_03_10 : b4RowContribution (![2, 2, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 15 = 24
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 15^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_10

theorem weighted_02_00_03_10 : b4RawGapContribution ![2, 0, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 10] = b4GapPatternWeight 0 3 10 * 0 :=
      b4GapContribution_from_row 2 0 3 10 0 row_02_00_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_10

def layers_02_00_03_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 44, 50, 53, 54, 54, 54, 54, 54, 54, 54, 54, 53, 50]]
#print axioms Paper7MomentGapNumeric.layers_02_00_03_11

theorem cells_02_00_03_11 : QTableValid (![2, 2, 5, 16] : Fin 4 → ℕ) layers_02_00_03_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_03_11

theorem valid_02_00_03_11 :
    SparseRowValid (![2, 2, 5, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_00_03_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 5, 16] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 5 + 16 = 25
      decide
    have hzsq : (∑ i, (((![2, 2, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 5^2 + 16^2 = 289
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_03_11
#print axioms Paper7MomentGapNumeric.valid_02_00_03_11

def qvalues_02_00_03_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_03_11

theorem row_02_00_03_11 : b4RowContribution (![2, 2, 5, 16] : Fin 4 → ℕ) = 54 := by
  calc
    b4RowContribution (![2, 2, 5, 16] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_02_00_03_11) :=
      sparseRow_sound (![2, 2, 5, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_00_03_11) valid_02_00_03_11
    _ = 54 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_03_11 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 54 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_03_11

theorem weighted_02_00_03_11 : b4RawGapContribution ![2, 0, 3, 11] = 648 := by
  calc
    b4RawGapContribution ![2, 0, 3, 11] = b4GapPatternWeight 0 3 11 * 54 :=
      b4GapContribution_from_row 2 0 3 11 54 row_02_00_03_11
    _ = 648 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_11

theorem row_02_00_03_12 : b4RowContribution (![2, 2, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 17 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 17^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_12

theorem weighted_02_00_03_12 : b4RawGapContribution ![2, 0, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 12] = b4GapPatternWeight 0 3 12 * 0 :=
      b4GapContribution_from_row 2 0 3 12 0 row_02_00_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_12

theorem row_02_00_03_13 : b4RowContribution (![2, 2, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 18 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 18^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_13

theorem weighted_02_00_03_13 : b4RawGapContribution ![2, 0, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 13] = b4GapPatternWeight 0 3 13 * 0 :=
      b4GapContribution_from_row 2 0 3 13 0 row_02_00_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_13

theorem row_02_00_03_14 : b4RowContribution (![2, 2, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 19 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 19^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_14

theorem weighted_02_00_03_14 : b4RawGapContribution ![2, 0, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 14] = b4GapPatternWeight 0 3 14 * 0 :=
      b4GapContribution_from_row 2 0 3 14 0 row_02_00_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_14

theorem row_02_00_03_15 : b4RowContribution (![2, 2, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 20 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 20^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_15

theorem weighted_02_00_03_15 : b4RawGapContribution ![2, 0, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 15] = b4GapPatternWeight 0 3 15 * 0 :=
      b4GapContribution_from_row 2 0 3 15 0 row_02_00_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_15

theorem row_02_00_03_16 : b4RowContribution (![2, 2, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 21 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 21^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_16

theorem weighted_02_00_03_16 : b4RawGapContribution ![2, 0, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 16] = b4GapPatternWeight 0 3 16 * 0 :=
      b4GapContribution_from_row 2 0 3 16 0 row_02_00_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_16

theorem row_02_00_03_17 : b4RowContribution (![2, 2, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 22 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 22^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_17

theorem weighted_02_00_03_17 : b4RawGapContribution ![2, 0, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 17] = b4GapPatternWeight 0 3 17 * 0 :=
      b4GapContribution_from_row 2 0 3 17 0 row_02_00_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_17

theorem row_02_00_03_18 : b4RowContribution (![2, 2, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 23 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 562 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 23^2 = 562
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_18

theorem weighted_02_00_03_18 : b4RawGapContribution ![2, 0, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 18] = b4GapPatternWeight 0 3 18 * 0 :=
      b4GapContribution_from_row 2 0 3 18 0 row_02_00_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_18

theorem row_02_00_03_19 : b4RowContribution (![2, 2, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 24 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 609 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 24^2 = 609
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_19

theorem weighted_02_00_03_19 : b4RawGapContribution ![2, 0, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 19] = b4GapPatternWeight 0 3 19 * 0 :=
      b4GapContribution_from_row 2 0 3 19 0 row_02_00_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_19

theorem row_02_00_03_20 : b4RowContribution (![2, 2, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 25 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 658 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 25^2 = 658
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_20

theorem weighted_02_00_03_20 : b4RawGapContribution ![2, 0, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 20] = b4GapPatternWeight 0 3 20 * 0 :=
      b4GapContribution_from_row 2 0 3 20 0 row_02_00_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_20

theorem row_02_00_03_21 : b4RowContribution (![2, 2, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 26 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 709 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 26^2 = 709
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_21

theorem weighted_02_00_03_21 : b4RawGapContribution ![2, 0, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 21] = b4GapPatternWeight 0 3 21 * 0 :=
      b4GapContribution_from_row 2 0 3 21 0 row_02_00_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_21

theorem row_02_00_03_22 : b4RowContribution (![2, 2, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 27 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 762 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 27^2 = 762
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_22

theorem weighted_02_00_03_22 : b4RawGapContribution ![2, 0, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 22] = b4GapPatternWeight 0 3 22 * 0 :=
      b4GapContribution_from_row 2 0 3 22 0 row_02_00_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_22

theorem row_02_00_03_23 : b4RowContribution (![2, 2, 5, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 5, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 5 + 28 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 5, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 817 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 5^2 + 28^2 = 817
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_03_23

theorem weighted_02_00_03_23 : b4RawGapContribution ![2, 0, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 3, 23] = b4GapPatternWeight 0 3 23 * 0 :=
      b4GapContribution_from_row 2 0 3 23 0 row_02_00_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_03_23

def dvalues_02_00_03 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1248, 0, 648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_03

theorem dblock_02_00_03 : b4GapPatternDBlock 2 0 3 = 1896 := by
  calc
    b4GapPatternDBlock 2 0 3 = ∑ d : Fin 24, dvalues_02_00_03 d := by
      apply b4GapDBlock_of_rows 2 0 3 dvalues_02_00_03
      intro d
      fin_cases d
      · exact weighted_02_00_03_00
      · exact weighted_02_00_03_01
      · exact weighted_02_00_03_02
      · exact weighted_02_00_03_03
      · exact weighted_02_00_03_04
      · exact weighted_02_00_03_05
      · exact weighted_02_00_03_06
      · exact weighted_02_00_03_07
      · exact weighted_02_00_03_08
      · exact weighted_02_00_03_09
      · exact weighted_02_00_03_10
      · exact weighted_02_00_03_11
      · exact weighted_02_00_03_12
      · exact weighted_02_00_03_13
      · exact weighted_02_00_03_14
      · exact weighted_02_00_03_15
      · exact weighted_02_00_03_16
      · exact weighted_02_00_03_17
      · exact weighted_02_00_03_18
      · exact weighted_02_00_03_19
      · exact weighted_02_00_03_20
      · exact weighted_02_00_03_21
      · exact weighted_02_00_03_22
      · exact weighted_02_00_03_23
    _ = 1896 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_03

end Paper7MomentGapNumeric
