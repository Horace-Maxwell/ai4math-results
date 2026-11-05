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

theorem row_00_01_05_00 : b4RowContribution (![0, 1, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 6 = 13
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 6^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_00

theorem weighted_00_01_05_00 : b4RawGapContribution ![0, 1, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 0] = b4GapPatternWeight 1 5 0 * 0 :=
      b4GapContribution_from_row 0 1 5 0 0 row_00_01_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_00

theorem row_00_01_05_01 : b4RowContribution (![0, 1, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 7 = 14
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 86 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 7^2 = 86
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_01

theorem weighted_00_01_05_01 : b4RawGapContribution ![0, 1, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 1] = b4GapPatternWeight 1 5 1 * 0 :=
      b4GapContribution_from_row 0 1 5 1 0 row_00_01_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_01

theorem row_00_01_05_02 : b4RowContribution (![0, 1, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 8 = 15
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 101 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 8^2 = 101
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_02

theorem weighted_00_01_05_02 : b4RawGapContribution ![0, 1, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 2] = b4GapPatternWeight 1 5 2 * 0 :=
      b4GapContribution_from_row 0 1 5 2 0 row_00_01_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_02

theorem row_00_01_05_03 : b4RowContribution (![0, 1, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 9 = 16
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 118 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 9^2 = 118
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_03

theorem weighted_00_01_05_03 : b4RawGapContribution ![0, 1, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 3] = b4GapPatternWeight 1 5 3 * 0 :=
      b4GapContribution_from_row 0 1 5 3 0 row_00_01_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_03

theorem row_00_01_05_04 : b4RowContribution (![0, 1, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 10 = 17
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 137 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 10^2 = 137
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_04

theorem weighted_00_01_05_04 : b4RawGapContribution ![0, 1, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 4] = b4GapPatternWeight 1 5 4 * 0 :=
      b4GapContribution_from_row 0 1 5 4 0 row_00_01_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_04

theorem row_00_01_05_05 : b4RowContribution (![0, 1, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 11 = 18
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 158 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 11^2 = 158
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_05

theorem weighted_00_01_05_05 : b4RawGapContribution ![0, 1, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 5] = b4GapPatternWeight 1 5 5 * 0 :=
      b4GapContribution_from_row 0 1 5 5 0 row_00_01_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_05

def layers_00_01_05_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 13, 11, 9, 7, 5, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_06

theorem cells_00_01_05_06 : QTableValid (![0, 1, 6, 12] : Fin 4 → ℕ) layers_00_01_05_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_06

theorem valid_00_01_05_06 :
    SparseRowValid (![0, 1, 6, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_01_05_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 12 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 181 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 12^2 = 181
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_06
#print axioms Paper7MomentGapNumeric.valid_00_01_05_06

def qvalues_00_01_05_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_06

theorem row_00_01_05_06 : b4RowContribution (![0, 1, 6, 12] : Fin 4 → ℕ) = 14 := by
  calc
    b4RowContribution (![0, 1, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_01_05_06) :=
      sparseRow_sound (![0, 1, 6, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_01_05_06) valid_00_01_05_06
    _ = 14 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_06 Q := by
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
        _ = 14 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_06

theorem weighted_00_01_05_06 : b4RawGapContribution ![0, 1, 5, 6] = 336 := by
  calc
    b4RawGapContribution ![0, 1, 5, 6] = b4GapPatternWeight 1 5 6 * 14 :=
      b4GapContribution_from_row 0 1 5 6 14 row_00_01_05_06
    _ = 336 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_06

def layers_00_01_05_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 14, 13, 11, 9, 7, 5]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_07

theorem cells_00_01_05_07 : QTableValid (![0, 1, 6, 13] : Fin 4 → ℕ) layers_00_01_05_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_07

theorem valid_00_01_05_07 :
    SparseRowValid (![0, 1, 6, 13] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_01_05_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 13] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 13 = 20
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 13^2 = 206
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_07
#print axioms Paper7MomentGapNumeric.valid_00_01_05_07

def qvalues_00_01_05_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_07

theorem row_00_01_05_07 : b4RowContribution (![0, 1, 6, 13] : Fin 4 → ℕ) = 7 := by
  calc
    b4RowContribution (![0, 1, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_00_01_05_07) :=
      sparseRow_sound (![0, 1, 6, 13] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_01_05_07) valid_00_01_05_07
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_07 Q := by
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
        _ = 7 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_07

theorem weighted_00_01_05_07 : b4RawGapContribution ![0, 1, 5, 7] = 168 := by
  calc
    b4RawGapContribution ![0, 1, 5, 7] = b4GapPatternWeight 1 5 7 * 7 :=
      b4GapContribution_from_row 0 1 5 7 7 row_00_01_05_07
    _ = 168 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_07

def layers_00_01_05_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 14, 14, 13, 11, 9, 7]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_08

theorem cells_00_01_05_08 : QTableValid (![0, 1, 6, 14] : Fin 4 → ℕ) layers_00_01_05_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_08

theorem valid_00_01_05_08 :
    SparseRowValid (![0, 1, 6, 14] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_05_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 14 = 21
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 14^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_08
#print axioms Paper7MomentGapNumeric.valid_00_01_05_08

def qvalues_00_01_05_08 : Fin 19 → ℕ := ![0, 0, 5, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_08

theorem row_00_01_05_08 : b4RowContribution (![0, 1, 6, 14] : Fin 4 → ℕ) = 33 := by
  calc
    b4RowContribution (![0, 1, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_05_08) :=
      sparseRow_sound (![0, 1, 6, 14] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_05_08) valid_00_01_05_08
    _ = 33 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_08 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 33 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_08

theorem weighted_00_01_05_08 : b4RawGapContribution ![0, 1, 5, 8] = 792 := by
  calc
    b4RawGapContribution ![0, 1, 5, 8] = b4GapPatternWeight 1 5 8 * 33 :=
      b4GapContribution_from_row 0 1 5 8 33 row_00_01_05_08
    _ = 792 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_08

theorem row_00_01_05_09 : b4RowContribution (![0, 1, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 15] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 15 = 22
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 15^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_09

theorem weighted_00_01_05_09 : b4RawGapContribution ![0, 1, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 9] = b4GapPatternWeight 1 5 9 * 0 :=
      b4GapContribution_from_row 0 1 5 9 0 row_00_01_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_09

def layers_00_01_05_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 13, 11]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_10

theorem cells_00_01_05_10 : QTableValid (![0, 1, 6, 16] : Fin 4 → ℕ) layers_00_01_05_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_10

theorem valid_00_01_05_10 :
    SparseRowValid (![0, 1, 6, 16] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_05_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 16] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 16 = 23
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 16^2 = 293
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_10
#print axioms Paper7MomentGapNumeric.valid_00_01_05_10

def qvalues_00_01_05_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_10

theorem row_00_01_05_10 : b4RowContribution (![0, 1, 6, 16] : Fin 4 → ℕ) = 14 := by
  calc
    b4RowContribution (![0, 1, 6, 16] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_01_05_10) :=
      sparseRow_sound (![0, 1, 6, 16] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_05_10) valid_00_01_05_10
    _ = 14 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_10 Q := by
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
        _ = 14 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_10

theorem weighted_00_01_05_10 : b4RawGapContribution ![0, 1, 5, 10] = 336 := by
  calc
    b4RawGapContribution ![0, 1, 5, 10] = b4GapPatternWeight 1 5 10 * 14 :=
      b4GapContribution_from_row 0 1 5 10 14 row_00_01_05_10
    _ = 336 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_10

theorem row_00_01_05_11 : b4RowContribution (![0, 1, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 17 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 17^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_11

theorem weighted_00_01_05_11 : b4RawGapContribution ![0, 1, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 11] = b4GapPatternWeight 1 5 11 * 0 :=
      b4GapContribution_from_row 0 1 5 11 0 row_00_01_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_11

theorem row_00_01_05_12 : b4RowContribution (![0, 1, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 18 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 18^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_12

theorem weighted_00_01_05_12 : b4RawGapContribution ![0, 1, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 12] = b4GapPatternWeight 1 5 12 * 0 :=
      b4GapContribution_from_row 0 1 5 12 0 row_00_01_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_12

theorem row_00_01_05_13 : b4RowContribution (![0, 1, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 19 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 19^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_13

theorem weighted_00_01_05_13 : b4RawGapContribution ![0, 1, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 13] = b4GapPatternWeight 1 5 13 * 0 :=
      b4GapContribution_from_row 0 1 5 13 0 row_00_01_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_13

theorem row_00_01_05_14 : b4RowContribution (![0, 1, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 20 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 20^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_14

theorem weighted_00_01_05_14 : b4RawGapContribution ![0, 1, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 14] = b4GapPatternWeight 1 5 14 * 0 :=
      b4GapContribution_from_row 0 1 5 14 0 row_00_01_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_14

theorem row_00_01_05_15 : b4RowContribution (![0, 1, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 21 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 478 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 21^2 = 478
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_15

theorem weighted_00_01_05_15 : b4RawGapContribution ![0, 1, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 15] = b4GapPatternWeight 1 5 15 * 0 :=
      b4GapContribution_from_row 0 1 5 15 0 row_00_01_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_15

def layers_00_01_05_16 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_16

theorem cells_00_01_05_16 : QTableValid (![0, 1, 6, 22] : Fin 4 → ℕ) layers_00_01_05_16 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_16

theorem valid_00_01_05_16 :
    SparseRowValid (![0, 1, 6, 22] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_16) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 22] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 22 = 29
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 521 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 22^2 = 521
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_16
#print axioms Paper7MomentGapNumeric.valid_00_01_05_16

def qvalues_00_01_05_16 : Fin 19 → ℕ := ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_16

theorem row_00_01_05_16 : b4RowContribution (![0, 1, 6, 22] : Fin 4 → ℕ) = 5 := by
  calc
    b4RowContribution (![0, 1, 6, 22] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_16) :=
      sparseRow_sound (![0, 1, 6, 22] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_16) valid_00_01_05_16
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_16 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 5 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_16

theorem weighted_00_01_05_16 : b4RawGapContribution ![0, 1, 5, 16] = 120 := by
  calc
    b4RawGapContribution ![0, 1, 5, 16] = b4GapPatternWeight 1 5 16 * 5 :=
      b4GapContribution_from_row 0 1 5 16 5 row_00_01_05_16
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_16

def layers_00_01_05_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14]]
#print axioms Paper7MomentGapNumeric.layers_00_01_05_17

theorem cells_00_01_05_17 : QTableValid (![0, 1, 6, 23] : Fin 4 → ℕ) layers_00_01_05_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_05_17

theorem valid_00_01_05_17 :
    SparseRowValid (![0, 1, 6, 23] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 6, 23] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 6 + 23 = 30
      decide
    have hzsq : (∑ i, (((![0, 1, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 6^2 + 23^2 = 566
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_05_17
#print axioms Paper7MomentGapNumeric.valid_00_01_05_17

def qvalues_00_01_05_17 : Fin 19 → ℕ := ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_05_17

theorem row_00_01_05_17 : b4RowContribution (![0, 1, 6, 23] : Fin 4 → ℕ) = 5 := by
  calc
    b4RowContribution (![0, 1, 6, 23] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_17) :=
      sparseRow_sound (![0, 1, 6, 23] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_01_05_17) valid_00_01_05_17
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_05_17 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 5 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_05_17

theorem weighted_00_01_05_17 : b4RawGapContribution ![0, 1, 5, 17] = 120 := by
  calc
    b4RawGapContribution ![0, 1, 5, 17] = b4GapPatternWeight 1 5 17 * 5 :=
      b4GapContribution_from_row 0 1 5 17 5 row_00_01_05_17
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_17

theorem row_00_01_05_18 : b4RowContribution (![0, 1, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 24 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 613 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 24^2 = 613
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_18

theorem weighted_00_01_05_18 : b4RawGapContribution ![0, 1, 5, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 18] = b4GapPatternWeight 1 5 18 * 0 :=
      b4GapContribution_from_row 0 1 5 18 0 row_00_01_05_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_18

theorem row_00_01_05_19 : b4RowContribution (![0, 1, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 25 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 662 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 25^2 = 662
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_19

theorem weighted_00_01_05_19 : b4RawGapContribution ![0, 1, 5, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 19] = b4GapPatternWeight 1 5 19 * 0 :=
      b4GapContribution_from_row 0 1 5 19 0 row_00_01_05_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_19

theorem row_00_01_05_20 : b4RowContribution (![0, 1, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 26 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 713 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 26^2 = 713
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_20

theorem weighted_00_01_05_20 : b4RawGapContribution ![0, 1, 5, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 20] = b4GapPatternWeight 1 5 20 * 0 :=
      b4GapContribution_from_row 0 1 5 20 0 row_00_01_05_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_20

theorem row_00_01_05_21 : b4RowContribution (![0, 1, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 27 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 766 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 27^2 = 766
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_21

theorem weighted_00_01_05_21 : b4RawGapContribution ![0, 1, 5, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 21] = b4GapPatternWeight 1 5 21 * 0 :=
      b4GapContribution_from_row 0 1 5 21 0 row_00_01_05_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_21

theorem row_00_01_05_22 : b4RowContribution (![0, 1, 6, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 28 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 821 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 28^2 = 821
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_22

theorem weighted_00_01_05_22 : b4RawGapContribution ![0, 1, 5, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 22] = b4GapPatternWeight 1 5 22 * 0 :=
      b4GapContribution_from_row 0 1 5 22 0 row_00_01_05_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_22

theorem row_00_01_05_23 : b4RowContribution (![0, 1, 6, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 29 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 878 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 29^2 = 878
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_23

theorem weighted_00_01_05_23 : b4RawGapContribution ![0, 1, 5, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 23] = b4GapPatternWeight 1 5 23 * 0 :=
      b4GapContribution_from_row 0 1 5 23 0 row_00_01_05_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_23

theorem row_00_01_05_24 : b4RowContribution (![0, 1, 6, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 6, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 6 + 30 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 6, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 937 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 6^2 + 30^2 = 937
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_05_24

theorem weighted_00_01_05_24 : b4RawGapContribution ![0, 1, 5, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 5, 24] = b4GapPatternWeight 1 5 24 * 0 :=
      b4GapContribution_from_row 0 1 5 24 0 row_00_01_05_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_05_24

def dvalues_00_01_05 : Fin 25 → ℕ := ![0, 0, 0, 0, 0, 0, 336, 168, 792, 0, 336, 0, 0, 0, 0, 0, 120, 120, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_05

theorem dblock_00_01_05 : b4GapPatternDBlock 0 1 5 = 1872 := by
  calc
    b4GapPatternDBlock 0 1 5 = ∑ d : Fin 25, dvalues_00_01_05 d := by
      apply b4GapDBlock_of_rows 0 1 5 dvalues_00_01_05
      intro d
      fin_cases d
      · exact weighted_00_01_05_00
      · exact weighted_00_01_05_01
      · exact weighted_00_01_05_02
      · exact weighted_00_01_05_03
      · exact weighted_00_01_05_04
      · exact weighted_00_01_05_05
      · exact weighted_00_01_05_06
      · exact weighted_00_01_05_07
      · exact weighted_00_01_05_08
      · exact weighted_00_01_05_09
      · exact weighted_00_01_05_10
      · exact weighted_00_01_05_11
      · exact weighted_00_01_05_12
      · exact weighted_00_01_05_13
      · exact weighted_00_01_05_14
      · exact weighted_00_01_05_15
      · exact weighted_00_01_05_16
      · exact weighted_00_01_05_17
      · exact weighted_00_01_05_18
      · exact weighted_00_01_05_19
      · exact weighted_00_01_05_20
      · exact weighted_00_01_05_21
      · exact weighted_00_01_05_22
      · exact weighted_00_01_05_23
      · exact weighted_00_01_05_24
    _ = 1872 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_05

end Paper7MomentGapNumeric
