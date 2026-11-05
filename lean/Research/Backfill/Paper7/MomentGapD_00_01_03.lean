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

def layers_00_01_03_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_03_00

theorem cells_00_01_03_00 : QTableValid (![0, 1, 4, 4] : Fin 4 → ℕ) layers_00_01_03_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_03_00

theorem valid_00_01_03_00 :
    SparseRowValid (![0, 1, 4, 4] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_01_03_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 4, 4] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 4 + 4 = 9
      decide
    have hzsq : (∑ i, (((![0, 1, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 33 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 4^2 + 4^2 = 33
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_03_00
#print axioms Paper7MomentGapNumeric.valid_00_01_03_00

def qvalues_00_01_03_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_03_00

theorem row_00_01_03_00 : b4RowContribution (![0, 1, 4, 4] : Fin 4 → ℕ) = 7 := by
  calc
    b4RowContribution (![0, 1, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_01_03_00) :=
      sparseRow_sound (![0, 1, 4, 4] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_01_03_00) valid_00_01_03_00
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_03_00 Q := by
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
        _ = 7 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_03_00

theorem weighted_00_01_03_00 : b4RawGapContribution ![0, 1, 3, 0] = 84 := by
  calc
    b4RawGapContribution ![0, 1, 3, 0] = b4GapPatternWeight 1 3 0 * 7 :=
      b4GapContribution_from_row 0 1 3 0 7 row_00_01_03_00
    _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_00

def layers_00_01_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_03_01

theorem cells_00_01_03_01 : QTableValid (![0, 1, 4, 5] : Fin 4 → ℕ) layers_00_01_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_03_01

theorem valid_00_01_03_01 :
    SparseRowValid (![0, 1, 4, 5] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 4, 5] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 4 + 5 = 10
      decide
    have hzsq : (∑ i, (((![0, 1, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 42 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 4^2 + 5^2 = 42
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_03_01
#print axioms Paper7MomentGapNumeric.valid_00_01_03_01

def qvalues_00_01_03_01 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_03_01

theorem row_00_01_03_01 : b4RowContribution (![0, 1, 4, 5] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![0, 1, 4, 5] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_01) :=
      sparseRow_sound (![0, 1, 4, 5] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_01) valid_00_01_03_01
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_03_01 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_03_01

theorem weighted_00_01_03_01 : b4RawGapContribution ![0, 1, 3, 1] = 240 := by
  calc
    b4RawGapContribution ![0, 1, 3, 1] = b4GapPatternWeight 1 3 1 * 10 :=
      b4GapContribution_from_row 0 1 3 1 10 row_00_01_03_01
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_01

theorem row_00_01_03_02 : b4RowContribution (![0, 1, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 6] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 6 = 11
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 53 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 6^2 = 53
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_02

theorem weighted_00_01_03_02 : b4RawGapContribution ![0, 1, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 2] = b4GapPatternWeight 1 3 2 * 0 :=
      b4GapContribution_from_row 0 1 3 2 0 row_00_01_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_02

theorem row_00_01_03_03 : b4RowContribution (![0, 1, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 7] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 7 = 12
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 66 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 7^2 = 66
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_03

theorem weighted_00_01_03_03 : b4RawGapContribution ![0, 1, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 3] = b4GapPatternWeight 1 3 3 * 0 :=
      b4GapContribution_from_row 0 1 3 3 0 row_00_01_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_03

theorem row_00_01_03_04 : b4RowContribution (![0, 1, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 8] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 8 = 13
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 8^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_04

theorem weighted_00_01_03_04 : b4RawGapContribution ![0, 1, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 4] = b4GapPatternWeight 1 3 4 * 0 :=
      b4GapContribution_from_row 0 1 3 4 0 row_00_01_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_04

theorem row_00_01_03_05 : b4RowContribution (![0, 1, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 9] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 9 = 14
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 98 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 9^2 = 98
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_05

theorem weighted_00_01_03_05 : b4RawGapContribution ![0, 1, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 5] = b4GapPatternWeight 1 3 5 * 0 :=
      b4GapContribution_from_row 0 1 3 5 0 row_00_01_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_05

theorem row_00_01_03_06 : b4RowContribution (![0, 1, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 10] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 10 = 15
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 117 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 10^2 = 117
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_06

theorem weighted_00_01_03_06 : b4RawGapContribution ![0, 1, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 6] = b4GapPatternWeight 1 3 6 * 0 :=
      b4GapContribution_from_row 0 1 3 6 0 row_00_01_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_06

theorem row_00_01_03_07 : b4RowContribution (![0, 1, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 11] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 11 = 16
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 11^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_07

theorem weighted_00_01_03_07 : b4RawGapContribution ![0, 1, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 7] = b4GapPatternWeight 1 3 7 * 0 :=
      b4GapContribution_from_row 0 1 3 7 0 row_00_01_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_07

theorem row_00_01_03_08 : b4RowContribution (![0, 1, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 12] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 12 = 17
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 12^2 = 161
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_08

theorem weighted_00_01_03_08 : b4RawGapContribution ![0, 1, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 8] = b4GapPatternWeight 1 3 8 * 0 :=
      b4GapContribution_from_row 0 1 3 8 0 row_00_01_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_08

def layers_00_01_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1]]
#print axioms Paper7MomentGapNumeric.layers_00_01_03_09

theorem cells_00_01_03_09 : QTableValid (![0, 1, 4, 13] : Fin 4 → ℕ) layers_00_01_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_03_09

theorem valid_00_01_03_09 :
    SparseRowValid (![0, 1, 4, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 4, 13] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 4 + 13 = 18
      decide
    have hzsq : (∑ i, (((![0, 1, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 4^2 + 13^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_03_09
#print axioms Paper7MomentGapNumeric.valid_00_01_03_09

def qvalues_00_01_03_09 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_03_09

theorem row_00_01_03_09 : b4RowContribution (![0, 1, 4, 13] : Fin 4 → ℕ) = 11 := by
  calc
    b4RowContribution (![0, 1, 4, 13] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_09) :=
      sparseRow_sound (![0, 1, 4, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_01_03_09) valid_00_01_03_09
    _ = 11 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_03_09 Q := by
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
        _ = 11 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_03_09

theorem weighted_00_01_03_09 : b4RawGapContribution ![0, 1, 3, 9] = 264 := by
  calc
    b4RawGapContribution ![0, 1, 3, 9] = b4GapPatternWeight 1 3 9 * 11 :=
      b4GapContribution_from_row 0 1 3 9 11 row_00_01_03_09
    _ = 264 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_09

def layers_00_01_03_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_03_10

theorem cells_00_01_03_10 : QTableValid (![0, 1, 4, 14] : Fin 4 → ℕ) layers_00_01_03_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_03_10

theorem valid_00_01_03_10 :
    SparseRowValid (![0, 1, 4, 14] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_03_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 4, 14] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 4 + 14 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 4^2 + 14^2 = 213
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_03_10
#print axioms Paper7MomentGapNumeric.valid_00_01_03_10

def qvalues_00_01_03_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_03_10

theorem row_00_01_03_10 : b4RowContribution (![0, 1, 4, 14] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 1, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_00_01_03_10) :=
      sparseRow_sound (![0, 1, 4, 14] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_03_10) valid_00_01_03_10
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_03_10 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_03_10

theorem weighted_00_01_03_10 : b4RawGapContribution ![0, 1, 3, 10] = 216 := by
  calc
    b4RawGapContribution ![0, 1, 3, 10] = b4GapPatternWeight 1 3 10 * 9 :=
      b4GapContribution_from_row 0 1 3 10 9 row_00_01_03_10
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_10

def layers_00_01_03_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 9, 7, 5]]
#print axioms Paper7MomentGapNumeric.layers_00_01_03_11

theorem cells_00_01_03_11 : QTableValid (![0, 1, 4, 15] : Fin 4 → ℕ) layers_00_01_03_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_03_11

theorem valid_00_01_03_11 :
    SparseRowValid (![0, 1, 4, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_01_03_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 4, 15] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 4 + 15 = 20
      decide
    have hzsq : (∑ i, (((![0, 1, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 4^2 + 15^2 = 242
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_03_11
#print axioms Paper7MomentGapNumeric.valid_00_01_03_11

def qvalues_00_01_03_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_03_11

theorem row_00_01_03_11 : b4RowContribution (![0, 1, 4, 15] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![0, 1, 4, 15] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_01_03_11) :=
      sparseRow_sound (![0, 1, 4, 15] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_01_03_11) valid_00_01_03_11
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_03_11 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_03_11

theorem weighted_00_01_03_11 : b4RawGapContribution ![0, 1, 3, 11] = 480 := by
  calc
    b4RawGapContribution ![0, 1, 3, 11] = b4GapPatternWeight 1 3 11 * 20 :=
      b4GapContribution_from_row 0 1 3 11 20 row_00_01_03_11
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_11

theorem row_00_01_03_12 : b4RowContribution (![0, 1, 4, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 16] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 16 = 21
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 16^2 = 273
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_12

theorem weighted_00_01_03_12 : b4RawGapContribution ![0, 1, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 12] = b4GapPatternWeight 1 3 12 * 0 :=
      b4GapContribution_from_row 0 1 3 12 0 row_00_01_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_12

theorem row_00_01_03_13 : b4RowContribution (![0, 1, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 17] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 17 = 22
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 17^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_13

theorem weighted_00_01_03_13 : b4RawGapContribution ![0, 1, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 13] = b4GapPatternWeight 1 3 13 * 0 :=
      b4GapContribution_from_row 0 1 3 13 0 row_00_01_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_13

theorem row_00_01_03_14 : b4RowContribution (![0, 1, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 18] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 18 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 18^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_14

theorem weighted_00_01_03_14 : b4RawGapContribution ![0, 1, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 14] = b4GapPatternWeight 1 3 14 * 0 :=
      b4GapContribution_from_row 0 1 3 14 0 row_00_01_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_14

theorem row_00_01_03_15 : b4RowContribution (![0, 1, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 19] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 19 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 19^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_15

theorem weighted_00_01_03_15 : b4RawGapContribution ![0, 1, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 15] = b4GapPatternWeight 1 3 15 * 0 :=
      b4GapContribution_from_row 0 1 3 15 0 row_00_01_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_15

theorem row_00_01_03_16 : b4RowContribution (![0, 1, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 20] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 20 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 20^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_16

theorem weighted_00_01_03_16 : b4RawGapContribution ![0, 1, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 16] = b4GapPatternWeight 1 3 16 * 0 :=
      b4GapContribution_from_row 0 1 3 16 0 row_00_01_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_16

theorem row_00_01_03_17 : b4RowContribution (![0, 1, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 21] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 21 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 21^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_17

theorem weighted_00_01_03_17 : b4RawGapContribution ![0, 1, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 17] = b4GapPatternWeight 1 3 17 * 0 :=
      b4GapContribution_from_row 0 1 3 17 0 row_00_01_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_17

theorem row_00_01_03_18 : b4RowContribution (![0, 1, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 22] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 22 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 22^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_18

theorem weighted_00_01_03_18 : b4RawGapContribution ![0, 1, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 18] = b4GapPatternWeight 1 3 18 * 0 :=
      b4GapContribution_from_row 0 1 3 18 0 row_00_01_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_18

theorem row_00_01_03_19 : b4RowContribution (![0, 1, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 23] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 23 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 23^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_19

theorem weighted_00_01_03_19 : b4RawGapContribution ![0, 1, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 19] = b4GapPatternWeight 1 3 19 * 0 :=
      b4GapContribution_from_row 0 1 3 19 0 row_00_01_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_19

theorem row_00_01_03_20 : b4RowContribution (![0, 1, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 24] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 24 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 593 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 24^2 = 593
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_20

theorem weighted_00_01_03_20 : b4RawGapContribution ![0, 1, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 20] = b4GapPatternWeight 1 3 20 * 0 :=
      b4GapContribution_from_row 0 1 3 20 0 row_00_01_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_20

theorem row_00_01_03_21 : b4RowContribution (![0, 1, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 25] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 25 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 642 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 25^2 = 642
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_21

theorem weighted_00_01_03_21 : b4RawGapContribution ![0, 1, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 21] = b4GapPatternWeight 1 3 21 * 0 :=
      b4GapContribution_from_row 0 1 3 21 0 row_00_01_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_21

theorem row_00_01_03_22 : b4RowContribution (![0, 1, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 26] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 26 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 693 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 26^2 = 693
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_22

theorem weighted_00_01_03_22 : b4RawGapContribution ![0, 1, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 22] = b4GapPatternWeight 1 3 22 * 0 :=
      b4GapContribution_from_row 0 1 3 22 0 row_00_01_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_22

theorem row_00_01_03_23 : b4RowContribution (![0, 1, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 27] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 27 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 746 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 27^2 = 746
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_23

theorem weighted_00_01_03_23 : b4RawGapContribution ![0, 1, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 23] = b4GapPatternWeight 1 3 23 * 0 :=
      b4GapContribution_from_row 0 1 3 23 0 row_00_01_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_23

theorem row_00_01_03_24 : b4RowContribution (![0, 1, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 28] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 28 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 801 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 28^2 = 801
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_24

theorem weighted_00_01_03_24 : b4RawGapContribution ![0, 1, 3, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 24] = b4GapPatternWeight 1 3 24 * 0 :=
      b4GapContribution_from_row 0 1 3 24 0 row_00_01_03_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_24

theorem row_00_01_03_25 : b4RowContribution (![0, 1, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 29] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 29 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 858 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 29^2 = 858
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_25

theorem weighted_00_01_03_25 : b4RawGapContribution ![0, 1, 3, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 25] = b4GapPatternWeight 1 3 25 * 0 :=
      b4GapContribution_from_row 0 1 3 25 0 row_00_01_03_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_25

theorem row_00_01_03_26 : b4RowContribution (![0, 1, 4, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 30] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 30 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 917 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 30^2 = 917
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_26

theorem weighted_00_01_03_26 : b4RawGapContribution ![0, 1, 3, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 26] = b4GapPatternWeight 1 3 26 * 0 :=
      b4GapContribution_from_row 0 1 3 26 0 row_00_01_03_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_26

theorem row_00_01_03_27 : b4RowContribution (![0, 1, 4, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 31] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 31 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 978 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 31^2 = 978
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_27

theorem weighted_00_01_03_27 : b4RawGapContribution ![0, 1, 3, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 27] = b4GapPatternWeight 1 3 27 * 0 :=
      b4GapContribution_from_row 0 1 3 27 0 row_00_01_03_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_27

theorem row_00_01_03_28 : b4RowContribution (![0, 1, 4, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 4, 32] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 4 + 32 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 4, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1041 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 4^2 + 32^2 = 1041
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_03_28

theorem weighted_00_01_03_28 : b4RawGapContribution ![0, 1, 3, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 3, 28] = b4GapPatternWeight 1 3 28 * 0 :=
      b4GapContribution_from_row 0 1 3 28 0 row_00_01_03_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_03_28

def dvalues_00_01_03 : Fin 29 → ℕ := ![84, 240, 0, 0, 0, 0, 0, 0, 0, 264, 216, 480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_03

theorem dblock_00_01_03 : b4GapPatternDBlock 0 1 3 = 1284 := by
  calc
    b4GapPatternDBlock 0 1 3 = ∑ d : Fin 29, dvalues_00_01_03 d := by
      apply b4GapDBlock_of_rows 0 1 3 dvalues_00_01_03
      intro d
      fin_cases d
      · exact weighted_00_01_03_00
      · exact weighted_00_01_03_01
      · exact weighted_00_01_03_02
      · exact weighted_00_01_03_03
      · exact weighted_00_01_03_04
      · exact weighted_00_01_03_05
      · exact weighted_00_01_03_06
      · exact weighted_00_01_03_07
      · exact weighted_00_01_03_08
      · exact weighted_00_01_03_09
      · exact weighted_00_01_03_10
      · exact weighted_00_01_03_11
      · exact weighted_00_01_03_12
      · exact weighted_00_01_03_13
      · exact weighted_00_01_03_14
      · exact weighted_00_01_03_15
      · exact weighted_00_01_03_16
      · exact weighted_00_01_03_17
      · exact weighted_00_01_03_18
      · exact weighted_00_01_03_19
      · exact weighted_00_01_03_20
      · exact weighted_00_01_03_21
      · exact weighted_00_01_03_22
      · exact weighted_00_01_03_23
      · exact weighted_00_01_03_24
      · exact weighted_00_01_03_25
      · exact weighted_00_01_03_26
      · exact weighted_00_01_03_27
      · exact weighted_00_01_03_28
    _ = 1284 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_03

end Paper7MomentGapNumeric
