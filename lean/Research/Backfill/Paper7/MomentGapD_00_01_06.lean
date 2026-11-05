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

theorem row_00_01_06_00 : b4RowContribution (![0, 1, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 7 = 15
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 7^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_00

theorem weighted_00_01_06_00 : b4RawGapContribution ![0, 1, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 0] = b4GapPatternWeight 1 6 0 * 0 :=
      b4GapContribution_from_row 0 1 6 0 0 row_00_01_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_00

theorem row_00_01_06_01 : b4RowContribution (![0, 1, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 8 = 16
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 8^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_01

theorem weighted_00_01_06_01 : b4RawGapContribution ![0, 1, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 1] = b4GapPatternWeight 1 6 1 * 0 :=
      b4GapContribution_from_row 0 1 6 1 0 row_00_01_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_01

theorem row_00_01_06_02 : b4RowContribution (![0, 1, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 9 = 17
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 131 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 9^2 = 131
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_02

theorem weighted_00_01_06_02 : b4RawGapContribution ![0, 1, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 2] = b4GapPatternWeight 1 6 2 * 0 :=
      b4GapContribution_from_row 0 1 6 2 0 row_00_01_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_02

theorem row_00_01_06_03 : b4RowContribution (![0, 1, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 10 = 18
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 10^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_03

theorem weighted_00_01_06_03 : b4RawGapContribution ![0, 1, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 3] = b4GapPatternWeight 1 6 3 * 0 :=
      b4GapContribution_from_row 0 1 6 3 0 row_00_01_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_03

def layers_00_01_06_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 16, 16, 15, 13, 11, 9, 7, 5, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_06_04

theorem cells_00_01_06_04 : QTableValid (![0, 1, 7, 11] : Fin 4 → ℕ) layers_00_01_06_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_06_04

theorem valid_00_01_06_04 :
    SparseRowValid (![0, 1, 7, 11] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_06_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 7, 11] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 7 + 11 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 7^2 + 11^2 = 171
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_06_04
#print axioms Paper7MomentGapNumeric.valid_00_01_06_04

def qvalues_00_01_06_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_06_04

theorem row_00_01_06_04 : b4RowContribution (![0, 1, 7, 11] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 1, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_01_06_04) :=
      sparseRow_sound (![0, 1, 7, 11] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_06_04) valid_00_01_06_04
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_06_04 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_06_04

theorem weighted_00_01_06_04 : b4RawGapContribution ![0, 1, 6, 4] = 360 := by
  calc
    b4RawGapContribution ![0, 1, 6, 4] = b4GapPatternWeight 1 6 4 * 15 :=
      b4GapContribution_from_row 0 1 6 4 15 row_00_01_06_04
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_04

theorem row_00_01_06_05 : b4RowContribution (![0, 1, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 12] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 12 = 20
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 12^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_05

theorem weighted_00_01_06_05 : b4RawGapContribution ![0, 1, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 5] = b4GapPatternWeight 1 6 5 * 0 :=
      b4GapContribution_from_row 0 1 6 5 0 row_00_01_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_05

def layers_00_01_06_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 16, 16, 16, 16, 15, 13, 11, 9, 7]]
#print axioms Paper7MomentGapNumeric.layers_00_01_06_06

theorem cells_00_01_06_06 : QTableValid (![0, 1, 7, 13] : Fin 4 → ℕ) layers_00_01_06_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_06_06

theorem valid_00_01_06_06 :
    SparseRowValid (![0, 1, 7, 13] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_06_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 7, 13] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 7 + 13 = 21
      decide
    have hzsq : (∑ i, (((![0, 1, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 7^2 + 13^2 = 219
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_06_06
#print axioms Paper7MomentGapNumeric.valid_00_01_06_06

def qvalues_00_01_06_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 13, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_06_06

theorem row_00_01_06_06 : b4RowContribution (![0, 1, 7, 13] : Fin 4 → ℕ) = 29 := by
  calc
    b4RowContribution (![0, 1, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_06_06) :=
      sparseRow_sound (![0, 1, 7, 13] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_06_06) valid_00_01_06_06
    _ = 29 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_06_06 Q := by
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
        _ = 29 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_06_06

theorem weighted_00_01_06_06 : b4RawGapContribution ![0, 1, 6, 6] = 696 := by
  calc
    b4RawGapContribution ![0, 1, 6, 6] = b4GapPatternWeight 1 6 6 * 29 :=
      b4GapContribution_from_row 0 1 6 6 29 row_00_01_06_06
    _ = 696 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_06

theorem row_00_01_06_07 : b4RowContribution (![0, 1, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 14] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 14 = 22
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 14^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_07

theorem weighted_00_01_06_07 : b4RawGapContribution ![0, 1, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 7] = b4GapPatternWeight 1 6 7 * 0 :=
      b4GapContribution_from_row 0 1 6 7 0 row_00_01_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_07

def layers_00_01_06_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 16, 16, 16, 16, 16, 16, 15, 13, 11]]
#print axioms Paper7MomentGapNumeric.layers_00_01_06_08

theorem cells_00_01_06_08 : QTableValid (![0, 1, 7, 15] : Fin 4 → ℕ) layers_00_01_06_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_06_08

theorem valid_00_01_06_08 :
    SparseRowValid (![0, 1, 7, 15] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_01_06_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 7, 15] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 7 + 15 = 23
      decide
    have hzsq : (∑ i, (((![0, 1, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 7^2 + 15^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_06_08
#print axioms Paper7MomentGapNumeric.valid_00_01_06_08

def qvalues_00_01_06_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_06_08

theorem row_00_01_06_08 : b4RowContribution (![0, 1, 7, 15] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![0, 1, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_00_01_06_08) :=
      sparseRow_sound (![0, 1, 7, 15] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_01_06_08) valid_00_01_06_08
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_06_08 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_06_08

theorem weighted_00_01_06_08 : b4RawGapContribution ![0, 1, 6, 8] = 384 := by
  calc
    b4RawGapContribution ![0, 1, 6, 8] = b4GapPatternWeight 1 6 8 * 16 :=
      b4GapContribution_from_row 0 1 6 8 16 row_00_01_06_08
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_08

theorem row_00_01_06_09 : b4RowContribution (![0, 1, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 16] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 16 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 16^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_09

theorem weighted_00_01_06_09 : b4RawGapContribution ![0, 1, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 9] = b4GapPatternWeight 1 6 9 * 0 :=
      b4GapContribution_from_row 0 1 6 9 0 row_00_01_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_09

theorem row_00_01_06_10 : b4RowContribution (![0, 1, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 17 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 17^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_10

theorem weighted_00_01_06_10 : b4RawGapContribution ![0, 1, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 10] = b4GapPatternWeight 1 6 10 * 0 :=
      b4GapContribution_from_row 0 1 6 10 0 row_00_01_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_10

theorem row_00_01_06_11 : b4RowContribution (![0, 1, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 18 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 18^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_11

theorem weighted_00_01_06_11 : b4RawGapContribution ![0, 1, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 11] = b4GapPatternWeight 1 6 11 * 0 :=
      b4GapContribution_from_row 0 1 6 11 0 row_00_01_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_11

theorem row_00_01_06_12 : b4RowContribution (![0, 1, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 19 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 19^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_12

theorem weighted_00_01_06_12 : b4RawGapContribution ![0, 1, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 12] = b4GapPatternWeight 1 6 12 * 0 :=
      b4GapContribution_from_row 0 1 6 12 0 row_00_01_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_12

theorem row_00_01_06_13 : b4RowContribution (![0, 1, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 20 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 20^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_13

theorem weighted_00_01_06_13 : b4RawGapContribution ![0, 1, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 13] = b4GapPatternWeight 1 6 13 * 0 :=
      b4GapContribution_from_row 0 1 6 13 0 row_00_01_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_13

theorem row_00_01_06_14 : b4RowContribution (![0, 1, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 21 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 21^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_14

theorem weighted_00_01_06_14 : b4RawGapContribution ![0, 1, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 14] = b4GapPatternWeight 1 6 14 * 0 :=
      b4GapContribution_from_row 0 1 6 14 0 row_00_01_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_14

theorem row_00_01_06_15 : b4RowContribution (![0, 1, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 22 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 22^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_15

theorem weighted_00_01_06_15 : b4RawGapContribution ![0, 1, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 15] = b4GapPatternWeight 1 6 15 * 0 :=
      b4GapContribution_from_row 0 1 6 15 0 row_00_01_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_15

theorem row_00_01_06_16 : b4RowContribution (![0, 1, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 23 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 23^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_16

theorem weighted_00_01_06_16 : b4RawGapContribution ![0, 1, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 16] = b4GapPatternWeight 1 6 16 * 0 :=
      b4GapContribution_from_row 0 1 6 16 0 row_00_01_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_16

theorem row_00_01_06_17 : b4RowContribution (![0, 1, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 24 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 24^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_17

theorem weighted_00_01_06_17 : b4RawGapContribution ![0, 1, 6, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 17] = b4GapPatternWeight 1 6 17 * 0 :=
      b4GapContribution_from_row 0 1 6 17 0 row_00_01_06_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_17

theorem row_00_01_06_18 : b4RowContribution (![0, 1, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 25 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 675 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 25^2 = 675
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_18

theorem weighted_00_01_06_18 : b4RawGapContribution ![0, 1, 6, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 18] = b4GapPatternWeight 1 6 18 * 0 :=
      b4GapContribution_from_row 0 1 6 18 0 row_00_01_06_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_18

theorem row_00_01_06_19 : b4RowContribution (![0, 1, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 26 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 726 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 26^2 = 726
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_19

theorem weighted_00_01_06_19 : b4RawGapContribution ![0, 1, 6, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 19] = b4GapPatternWeight 1 6 19 * 0 :=
      b4GapContribution_from_row 0 1 6 19 0 row_00_01_06_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_19

theorem row_00_01_06_20 : b4RowContribution (![0, 1, 7, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 27 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 779 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 27^2 = 779
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_20

theorem weighted_00_01_06_20 : b4RawGapContribution ![0, 1, 6, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 20] = b4GapPatternWeight 1 6 20 * 0 :=
      b4GapContribution_from_row 0 1 6 20 0 row_00_01_06_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_20

theorem row_00_01_06_21 : b4RowContribution (![0, 1, 7, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 28 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 834 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 28^2 = 834
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_21

theorem weighted_00_01_06_21 : b4RawGapContribution ![0, 1, 6, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 21] = b4GapPatternWeight 1 6 21 * 0 :=
      b4GapContribution_from_row 0 1 6 21 0 row_00_01_06_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_21

theorem row_00_01_06_22 : b4RowContribution (![0, 1, 7, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 7, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 7 + 29 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 7, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 891 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 7^2 + 29^2 = 891
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_06_22

theorem weighted_00_01_06_22 : b4RawGapContribution ![0, 1, 6, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 6, 22] = b4GapPatternWeight 1 6 22 * 0 :=
      b4GapContribution_from_row 0 1 6 22 0 row_00_01_06_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_06_22

def dvalues_00_01_06 : Fin 23 → ℕ := ![0, 0, 0, 0, 360, 0, 696, 0, 384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_06

theorem dblock_00_01_06 : b4GapPatternDBlock 0 1 6 = 1440 := by
  calc
    b4GapPatternDBlock 0 1 6 = ∑ d : Fin 23, dvalues_00_01_06 d := by
      apply b4GapDBlock_of_rows 0 1 6 dvalues_00_01_06
      intro d
      fin_cases d
      · exact weighted_00_01_06_00
      · exact weighted_00_01_06_01
      · exact weighted_00_01_06_02
      · exact weighted_00_01_06_03
      · exact weighted_00_01_06_04
      · exact weighted_00_01_06_05
      · exact weighted_00_01_06_06
      · exact weighted_00_01_06_07
      · exact weighted_00_01_06_08
      · exact weighted_00_01_06_09
      · exact weighted_00_01_06_10
      · exact weighted_00_01_06_11
      · exact weighted_00_01_06_12
      · exact weighted_00_01_06_13
      · exact weighted_00_01_06_14
      · exact weighted_00_01_06_15
      · exact weighted_00_01_06_16
      · exact weighted_00_01_06_17
      · exact weighted_00_01_06_18
      · exact weighted_00_01_06_19
      · exact weighted_00_01_06_20
      · exact weighted_00_01_06_21
      · exact weighted_00_01_06_22
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_06

end Paper7MomentGapNumeric
