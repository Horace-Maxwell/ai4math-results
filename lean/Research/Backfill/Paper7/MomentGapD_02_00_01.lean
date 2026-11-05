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

theorem row_02_00_01_00 : b4RowContribution (![2, 2, 3, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 3] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 3 = 10
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 26 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 3^2 = 26
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_00

theorem weighted_02_00_01_00 : b4RawGapContribution ![2, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 2 0 1 0 0 row_02_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_00

def layers_02_00_01_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 31, 31, 26, 18, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_01

theorem cells_02_00_01_01 : QTableValid (![2, 2, 3, 4] : Fin 4 → ℕ) layers_02_00_01_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_01

theorem valid_02_00_01_01 :
    SparseRowValid (![2, 2, 3, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_00_01_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 4] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 4 = 11
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 33 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 4^2 = 33
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_01
#print axioms Paper7MomentGapNumeric.valid_02_00_01_01

def qvalues_02_00_01_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_01

theorem row_02_00_01_01 : b4RowContribution (![2, 2, 3, 4] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![2, 2, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_00_01_01) :=
      sparseRow_sound (![2, 2, 3, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_00_01_01) valid_02_00_01_01
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_01 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_01_01

theorem weighted_02_00_01_01 : b4RawGapContribution ![2, 0, 1, 1] = 120 := by
  calc
    b4RawGapContribution ![2, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 10 :=
      b4GapContribution_from_row 2 0 1 1 10 row_02_00_01_01
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_01

def layers_02_00_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 32, 34, 32, 26, 18, 10, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_02

theorem cells_02_00_01_02 : QTableValid (![2, 2, 3, 5] : Fin 4 → ℕ) layers_02_00_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_02

theorem valid_02_00_01_02 :
    SparseRowValid (![2, 2, 3, 5] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 5] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 5 = 12
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 42 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 5^2 = 42
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_02
#print axioms Paper7MomentGapNumeric.valid_02_00_01_02

def qvalues_02_00_01_02 : Fin 19 → ℕ := ![0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_02

theorem row_02_00_01_02 : b4RowContribution (![2, 2, 3, 5] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![2, 2, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_02) :=
      sparseRow_sound (![2, 2, 3, 5] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_02) valid_02_00_01_02
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_02 Q := by
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
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_01_02

theorem weighted_02_00_01_02 : b4RawGapContribution ![2, 0, 1, 2] = 216 := by
  calc
    b4RawGapContribution ![2, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 18 :=
      b4GapContribution_from_row 2 0 1 2 18 row_02_00_01_02
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_02

theorem row_02_00_01_03 : b4RowContribution (![2, 2, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 6 = 13
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 53 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 6^2 = 53
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_03

theorem weighted_02_00_01_03 : b4RawGapContribution ![2, 0, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 0 :=
      b4GapContribution_from_row 2 0 1 3 0 row_02_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_03

theorem row_02_00_01_04 : b4RowContribution (![2, 2, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 7 = 14
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 66 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 7^2 = 66
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_04

theorem weighted_02_00_01_04 : b4RawGapContribution ![2, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 2 0 1 4 0 row_02_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_04

theorem row_02_00_01_05 : b4RowContribution (![2, 2, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 8 = 15
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 8^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_05

theorem weighted_02_00_01_05 : b4RawGapContribution ![2, 0, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 0 :=
      b4GapContribution_from_row 2 0 1 5 0 row_02_00_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_05

theorem row_02_00_01_06 : b4RowContribution (![2, 2, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 9 = 16
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 98 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 9^2 = 98
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_06

theorem weighted_02_00_01_06 : b4RawGapContribution ![2, 0, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 0 :=
      b4GapContribution_from_row 2 0 1 6 0 row_02_00_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_06

theorem row_02_00_01_07 : b4RowContribution (![2, 2, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 10 = 17
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 117 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 10^2 = 117
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_07

theorem weighted_02_00_01_07 : b4RawGapContribution ![2, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 2 0 1 7 0 row_02_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_07

theorem row_02_00_01_08 : b4RowContribution (![2, 2, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 11 = 18
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 11^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_08

theorem weighted_02_00_01_08 : b4RawGapContribution ![2, 0, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 8] = b4GapPatternWeight 0 1 8 * 0 :=
      b4GapContribution_from_row 2 0 1 8 0 row_02_00_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_08

def layers_02_00_01_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 32, 35, 36, 36, 36, 36, 36, 36, 35, 32, 26, 18, 10, 4]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_09

theorem cells_02_00_01_09 : QTableValid (![2, 2, 3, 12] : Fin 4 → ℕ) layers_02_00_01_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_09

theorem valid_02_00_01_09 :
    SparseRowValid (![2, 2, 3, 12] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_02_00_01_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 12 = 19
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 12^2 = 161
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_09
#print axioms Paper7MomentGapNumeric.valid_02_00_01_09

def qvalues_02_00_01_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_09

theorem row_02_00_01_09 : b4RowContribution (![2, 2, 3, 12] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![2, 2, 3, 12] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_02_00_01_09) :=
      sparseRow_sound (![2, 2, 3, 12] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_02_00_01_09) valid_02_00_01_09
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_09 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_00_01_09

theorem weighted_02_00_01_09 : b4RawGapContribution ![2, 0, 1, 9] = 120 := by
  calc
    b4RawGapContribution ![2, 0, 1, 9] = b4GapPatternWeight 0 1 9 * 10 :=
      b4GapContribution_from_row 2 0 1 9 10 row_02_00_01_09
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_09

def layers_02_00_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 32, 35, 36, 36, 36, 36, 36, 36, 36, 35, 32, 26, 18, 10]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_10

theorem cells_02_00_01_10 : QTableValid (![2, 2, 3, 13] : Fin 4 → ℕ) layers_02_00_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_10

theorem valid_02_00_01_10 :
    SparseRowValid (![2, 2, 3, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 13] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 13 = 20
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 13^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_10
#print axioms Paper7MomentGapNumeric.valid_02_00_01_10

def qvalues_02_00_01_10 : Fin 19 → ℕ := ![0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_10

theorem row_02_00_01_10 : b4RowContribution (![2, 2, 3, 13] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![2, 2, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_10) :=
      sparseRow_sound (![2, 2, 3, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_00_01_10) valid_02_00_01_10
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_10 Q := by
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
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_01_10

theorem weighted_02_00_01_10 : b4RawGapContribution ![2, 0, 1, 10] = 216 := by
  calc
    b4RawGapContribution ![2, 0, 1, 10] = b4GapPatternWeight 0 1 10 * 18 :=
      b4GapContribution_from_row 2 0 1 10 18 row_02_00_01_10
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_10

def layers_02_00_01_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 32, 35, 36, 36, 36, 36, 36, 36, 36, 36, 35, 32, 26, 18]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_11

theorem cells_02_00_01_11 : QTableValid (![2, 2, 3, 14] : Fin 4 → ℕ) layers_02_00_01_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_11

theorem valid_02_00_01_11 :
    SparseRowValid (![2, 2, 3, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_01_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 14 = 21
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 14^2 = 213
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_11
#print axioms Paper7MomentGapNumeric.valid_02_00_01_11

def qvalues_02_00_01_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_11

theorem row_02_00_01_11 : b4RowContribution (![2, 2, 3, 14] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![2, 2, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_02_00_01_11) :=
      sparseRow_sound (![2, 2, 3, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_01_11) valid_02_00_01_11
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_11 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_01_11

theorem weighted_02_00_01_11 : b4RawGapContribution ![2, 0, 1, 11] = 432 := by
  calc
    b4RawGapContribution ![2, 0, 1, 11] = b4GapPatternWeight 0 1 11 * 36 :=
      b4GapContribution_from_row 2 0 1 11 36 row_02_00_01_11
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_11

def layers_02_00_01_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 26, 32, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 35, 32, 26]]
#print axioms Paper7MomentGapNumeric.layers_02_00_01_12

theorem cells_02_00_01_12 : QTableValid (![2, 2, 3, 15] : Fin 4 → ℕ) layers_02_00_01_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_01_12

theorem valid_02_00_01_12 :
    SparseRowValid (![2, 2, 3, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_00_01_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 3, 15] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 3 + 15 = 22
      decide
    have hzsq : (∑ i, (((![2, 2, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 3^2 + 15^2 = 242
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_01_12
#print axioms Paper7MomentGapNumeric.valid_02_00_01_12

def qvalues_02_00_01_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_01_12

theorem row_02_00_01_12 : b4RowContribution (![2, 2, 3, 15] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![2, 2, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_02_00_01_12) :=
      sparseRow_sound (![2, 2, 3, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_00_01_12) valid_02_00_01_12
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_01_12 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_01_12

theorem weighted_02_00_01_12 : b4RawGapContribution ![2, 0, 1, 12] = 432 := by
  calc
    b4RawGapContribution ![2, 0, 1, 12] = b4GapPatternWeight 0 1 12 * 36 :=
      b4GapContribution_from_row 2 0 1 12 36 row_02_00_01_12
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_12

theorem row_02_00_01_13 : b4RowContribution (![2, 2, 3, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 16] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 16 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 16^2 = 273
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_13

theorem weighted_02_00_01_13 : b4RawGapContribution ![2, 0, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 13] = b4GapPatternWeight 0 1 13 * 0 :=
      b4GapContribution_from_row 2 0 1 13 0 row_02_00_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_13

theorem row_02_00_01_14 : b4RowContribution (![2, 2, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 17 = 24
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 17^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_14

theorem weighted_02_00_01_14 : b4RawGapContribution ![2, 0, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 14] = b4GapPatternWeight 0 1 14 * 0 :=
      b4GapContribution_from_row 2 0 1 14 0 row_02_00_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_14

theorem row_02_00_01_15 : b4RowContribution (![2, 2, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 18 = 25
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 18^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_15

theorem weighted_02_00_01_15 : b4RawGapContribution ![2, 0, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 15] = b4GapPatternWeight 0 1 15 * 0 :=
      b4GapContribution_from_row 2 0 1 15 0 row_02_00_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_15

theorem row_02_00_01_16 : b4RowContribution (![2, 2, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 19 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 19^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_16

theorem weighted_02_00_01_16 : b4RawGapContribution ![2, 0, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 16] = b4GapPatternWeight 0 1 16 * 0 :=
      b4GapContribution_from_row 2 0 1 16 0 row_02_00_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_16

theorem row_02_00_01_17 : b4RowContribution (![2, 2, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 20 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 20^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_17

theorem weighted_02_00_01_17 : b4RawGapContribution ![2, 0, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 17] = b4GapPatternWeight 0 1 17 * 0 :=
      b4GapContribution_from_row 2 0 1 17 0 row_02_00_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_17

theorem row_02_00_01_18 : b4RowContribution (![2, 2, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 21 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 21^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_18

theorem weighted_02_00_01_18 : b4RawGapContribution ![2, 0, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 18] = b4GapPatternWeight 0 1 18 * 0 :=
      b4GapContribution_from_row 2 0 1 18 0 row_02_00_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_18

theorem row_02_00_01_19 : b4RowContribution (![2, 2, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 22] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 22 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 22^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_19

theorem weighted_02_00_01_19 : b4RawGapContribution ![2, 0, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 19] = b4GapPatternWeight 0 1 19 * 0 :=
      b4GapContribution_from_row 2 0 1 19 0 row_02_00_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_19

theorem row_02_00_01_20 : b4RowContribution (![2, 2, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 23] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 23 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 23^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_20

theorem weighted_02_00_01_20 : b4RawGapContribution ![2, 0, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 20] = b4GapPatternWeight 0 1 20 * 0 :=
      b4GapContribution_from_row 2 0 1 20 0 row_02_00_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_20

theorem row_02_00_01_21 : b4RowContribution (![2, 2, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 24 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 593 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 24^2 = 593
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_21

theorem weighted_02_00_01_21 : b4RawGapContribution ![2, 0, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 21] = b4GapPatternWeight 0 1 21 * 0 :=
      b4GapContribution_from_row 2 0 1 21 0 row_02_00_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_21

theorem row_02_00_01_22 : b4RowContribution (![2, 2, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 25 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 642 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 25^2 = 642
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_22

theorem weighted_02_00_01_22 : b4RawGapContribution ![2, 0, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 22] = b4GapPatternWeight 0 1 22 * 0 :=
      b4GapContribution_from_row 2 0 1 22 0 row_02_00_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_22

theorem row_02_00_01_23 : b4RowContribution (![2, 2, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 26 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 693 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 26^2 = 693
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_23

theorem weighted_02_00_01_23 : b4RawGapContribution ![2, 0, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 23] = b4GapPatternWeight 0 1 23 * 0 :=
      b4GapContribution_from_row 2 0 1 23 0 row_02_00_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_23

theorem row_02_00_01_24 : b4RowContribution (![2, 2, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 27 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 746 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 27^2 = 746
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_24

theorem weighted_02_00_01_24 : b4RawGapContribution ![2, 0, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 24] = b4GapPatternWeight 0 1 24 * 0 :=
      b4GapContribution_from_row 2 0 1 24 0 row_02_00_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_24

theorem row_02_00_01_25 : b4RowContribution (![2, 2, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 28 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 801 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 28^2 = 801
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_25

theorem weighted_02_00_01_25 : b4RawGapContribution ![2, 0, 1, 25] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 25] = b4GapPatternWeight 0 1 25 * 0 :=
      b4GapContribution_from_row 2 0 1 25 0 row_02_00_01_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_25

theorem row_02_00_01_26 : b4RowContribution (![2, 2, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 29 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 858 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 29^2 = 858
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_26

theorem weighted_02_00_01_26 : b4RawGapContribution ![2, 0, 1, 26] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 26] = b4GapPatternWeight 0 1 26 * 0 :=
      b4GapContribution_from_row 2 0 1 26 0 row_02_00_01_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_26

theorem row_02_00_01_27 : b4RowContribution (![2, 2, 3, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 3, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 3 + 30 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 917 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 3^2 + 30^2 = 917
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_01_27

theorem weighted_02_00_01_27 : b4RawGapContribution ![2, 0, 1, 27] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 1, 27] = b4GapPatternWeight 0 1 27 * 0 :=
      b4GapContribution_from_row 2 0 1 27 0 row_02_00_01_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_01_27

def dvalues_02_00_01 : Fin 28 → ℕ := ![0, 120, 216, 0, 0, 0, 0, 0, 0, 120, 216, 432, 432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_01

theorem dblock_02_00_01 : b4GapPatternDBlock 2 0 1 = 1536 := by
  calc
    b4GapPatternDBlock 2 0 1 = ∑ d : Fin 28, dvalues_02_00_01 d := by
      apply b4GapDBlock_of_rows 2 0 1 dvalues_02_00_01
      intro d
      fin_cases d
      · exact weighted_02_00_01_00
      · exact weighted_02_00_01_01
      · exact weighted_02_00_01_02
      · exact weighted_02_00_01_03
      · exact weighted_02_00_01_04
      · exact weighted_02_00_01_05
      · exact weighted_02_00_01_06
      · exact weighted_02_00_01_07
      · exact weighted_02_00_01_08
      · exact weighted_02_00_01_09
      · exact weighted_02_00_01_10
      · exact weighted_02_00_01_11
      · exact weighted_02_00_01_12
      · exact weighted_02_00_01_13
      · exact weighted_02_00_01_14
      · exact weighted_02_00_01_15
      · exact weighted_02_00_01_16
      · exact weighted_02_00_01_17
      · exact weighted_02_00_01_18
      · exact weighted_02_00_01_19
      · exact weighted_02_00_01_20
      · exact weighted_02_00_01_21
      · exact weighted_02_00_01_22
      · exact weighted_02_00_01_23
      · exact weighted_02_00_01_24
      · exact weighted_02_00_01_25
      · exact weighted_02_00_01_26
      · exact weighted_02_00_01_27
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_01

end Paper7MomentGapNumeric
