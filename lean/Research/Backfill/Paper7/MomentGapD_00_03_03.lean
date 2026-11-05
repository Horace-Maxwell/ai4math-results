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

theorem row_00_03_03_00 : b4RowContribution (![0, 3, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 6 = 15
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 6^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_00

theorem weighted_00_03_03_00 : b4RawGapContribution ![0, 3, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 0] = b4GapPatternWeight 3 3 0 * 0 :=
      b4GapContribution_from_row 0 3 3 0 0 row_00_03_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_00

theorem row_00_03_03_01 : b4RowContribution (![0, 3, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 7 = 16
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 94 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 7^2 = 94
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_01

theorem weighted_00_03_03_01 : b4RawGapContribution ![0, 3, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 1] = b4GapPatternWeight 3 3 1 * 0 :=
      b4GapContribution_from_row 0 3 3 1 0 row_00_03_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_01

theorem row_00_03_03_02 : b4RowContribution (![0, 3, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 8 = 17
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 8^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_02

theorem weighted_00_03_03_02 : b4RawGapContribution ![0, 3, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 2] = b4GapPatternWeight 3 3 2 * 0 :=
      b4GapContribution_from_row 0 3 3 2 0 row_00_03_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_02

theorem row_00_03_03_03 : b4RowContribution (![0, 3, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 9 = 18
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 9^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_03

theorem weighted_00_03_03_03 : b4RawGapContribution ![0, 3, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 3] = b4GapPatternWeight 3 3 3 * 0 :=
      b4GapContribution_from_row 0 3 3 3 0 row_00_03_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_03

theorem row_00_03_03_04 : b4RowContribution (![0, 3, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 10 = 19
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 10^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_04

theorem weighted_00_03_03_04 : b4RawGapContribution ![0, 3, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 4] = b4GapPatternWeight 3 3 4 * 0 :=
      b4GapContribution_from_row 0 3 3 4 0 row_00_03_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_04

def layers_00_03_03_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 27, 28, 28, 28, 27, 25, 22, 18, 14, 10, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_03_03_05

theorem cells_00_03_03_05 : QTableValid (![0, 3, 6, 11] : Fin 4 → ℕ) layers_00_03_03_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_03_05

theorem valid_00_03_03_05 :
    SparseRowValid (![0, 3, 6, 11] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_03_03_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 6, 11] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 6 + 11 = 20
      decide
    have hzsq : (∑ i, (((![0, 3, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 6^2 + 11^2 = 166
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_03_05
#print axioms Paper7MomentGapNumeric.valid_00_03_03_05

def qvalues_00_03_03_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_03_05

theorem row_00_03_03_05 : b4RowContribution (![0, 3, 6, 11] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![0, 3, 6, 11] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_00_03_03_05) :=
      sparseRow_sound (![0, 3, 6, 11] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_03_03_05) valid_00_03_03_05
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_03_05 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_03_05

theorem weighted_00_03_03_05 : b4RawGapContribution ![0, 3, 3, 5] = 600 := by
  calc
    b4RawGapContribution ![0, 3, 3, 5] = b4GapPatternWeight 3 3 5 * 25 :=
      b4GapContribution_from_row 0 3 3 5 25 row_00_03_03_05
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_05

def layers_00_03_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 27, 28, 28, 28, 28, 27, 25, 22, 18, 14, 10]]
#print axioms Paper7MomentGapNumeric.layers_00_03_03_06

theorem cells_00_03_03_06 : QTableValid (![0, 3, 6, 12] : Fin 4 → ℕ) layers_00_03_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_03_06

theorem valid_00_03_03_06 :
    SparseRowValid (![0, 3, 6, 12] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_03_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 6, 12] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 6 + 12 = 21
      decide
    have hzsq : (∑ i, (((![0, 3, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 6^2 + 12^2 = 189
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_03_06
#print axioms Paper7MomentGapNumeric.valid_00_03_03_06

def qvalues_00_03_03_06 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_03_06

theorem row_00_03_03_06 : b4RowContribution (![0, 3, 6, 12] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 3, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_00_03_03_06) :=
      sparseRow_sound (![0, 3, 6, 12] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_03_03_06) valid_00_03_03_06
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_03_06 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_03_03_06

theorem weighted_00_03_03_06 : b4RawGapContribution ![0, 3, 3, 6] = 24 := by
  calc
    b4RawGapContribution ![0, 3, 3, 6] = b4GapPatternWeight 3 3 6 * 1 :=
      b4GapContribution_from_row 0 3 3 6 1 row_00_03_03_06
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_06

theorem row_00_03_03_07 : b4RowContribution (![0, 3, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 13 = 22
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 13^2 = 214
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_07

theorem weighted_00_03_03_07 : b4RawGapContribution ![0, 3, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 7] = b4GapPatternWeight 3 3 7 * 0 :=
      b4GapContribution_from_row 0 3 3 7 0 row_00_03_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_07

def layers_00_03_03_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 27, 28, 28, 28, 28, 28, 28, 27, 25, 22, 18]]
#print axioms Paper7MomentGapNumeric.layers_00_03_03_08

theorem cells_00_03_03_08 : QTableValid (![0, 3, 6, 14] : Fin 4 → ℕ) layers_00_03_03_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_03_08

theorem valid_00_03_03_08 :
    SparseRowValid (![0, 3, 6, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_03_03_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 6, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 6 + 14 = 23
      decide
    have hzsq : (∑ i, (((![0, 3, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 6^2 + 14^2 = 241
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_03_08
#print axioms Paper7MomentGapNumeric.valid_00_03_03_08

def qvalues_00_03_03_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_03_08

theorem row_00_03_03_08 : b4RowContribution (![0, 3, 6, 14] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![0, 3, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_03_03_08) :=
      sparseRow_sound (![0, 3, 6, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_03_03_08) valid_00_03_03_08
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_03_08 Q := by
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
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_03_08

theorem weighted_00_03_03_08 : b4RawGapContribution ![0, 3, 3, 8] = 600 := by
  calc
    b4RawGapContribution ![0, 3, 3, 8] = b4GapPatternWeight 3 3 8 * 25 :=
      b4GapContribution_from_row 0 3 3 8 25 row_00_03_03_08
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_08

theorem row_00_03_03_09 : b4RowContribution (![0, 3, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 15 = 24
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 15^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_09

theorem weighted_00_03_03_09 : b4RawGapContribution ![0, 3, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 9] = b4GapPatternWeight 3 3 9 * 0 :=
      b4GapContribution_from_row 0 3 3 9 0 row_00_03_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_09

theorem row_00_03_03_10 : b4RowContribution (![0, 3, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 16] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 16 = 25
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 16^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_10

theorem weighted_00_03_03_10 : b4RawGapContribution ![0, 3, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 10] = b4GapPatternWeight 3 3 10 * 0 :=
      b4GapContribution_from_row 0 3 3 10 0 row_00_03_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_10

theorem row_00_03_03_11 : b4RowContribution (![0, 3, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 17 = 26
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 17^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_11

theorem weighted_00_03_03_11 : b4RawGapContribution ![0, 3, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 11] = b4GapPatternWeight 3 3 11 * 0 :=
      b4GapContribution_from_row 0 3 3 11 0 row_00_03_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_11

theorem row_00_03_03_12 : b4RowContribution (![0, 3, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 18 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 18^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_12

theorem weighted_00_03_03_12 : b4RawGapContribution ![0, 3, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 12] = b4GapPatternWeight 3 3 12 * 0 :=
      b4GapContribution_from_row 0 3 3 12 0 row_00_03_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_12

theorem row_00_03_03_13 : b4RowContribution (![0, 3, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 19 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 19^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_13

theorem weighted_00_03_03_13 : b4RawGapContribution ![0, 3, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 13] = b4GapPatternWeight 3 3 13 * 0 :=
      b4GapContribution_from_row 0 3 3 13 0 row_00_03_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_13

theorem row_00_03_03_14 : b4RowContribution (![0, 3, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 20 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 20^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_14

theorem weighted_00_03_03_14 : b4RawGapContribution ![0, 3, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 14] = b4GapPatternWeight 3 3 14 * 0 :=
      b4GapContribution_from_row 0 3 3 14 0 row_00_03_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_14

theorem row_00_03_03_15 : b4RowContribution (![0, 3, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 21 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 21^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_15

theorem weighted_00_03_03_15 : b4RawGapContribution ![0, 3, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 15] = b4GapPatternWeight 3 3 15 * 0 :=
      b4GapContribution_from_row 0 3 3 15 0 row_00_03_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_15

theorem row_00_03_03_16 : b4RowContribution (![0, 3, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 22 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 22^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_16

theorem weighted_00_03_03_16 : b4RawGapContribution ![0, 3, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 16] = b4GapPatternWeight 3 3 16 * 0 :=
      b4GapContribution_from_row 0 3 3 16 0 row_00_03_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_16

theorem row_00_03_03_17 : b4RowContribution (![0, 3, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 23 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 574 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 23^2 = 574
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_17

theorem weighted_00_03_03_17 : b4RawGapContribution ![0, 3, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 17] = b4GapPatternWeight 3 3 17 * 0 :=
      b4GapContribution_from_row 0 3 3 17 0 row_00_03_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_17

theorem row_00_03_03_18 : b4RowContribution (![0, 3, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 24 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 621 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 24^2 = 621
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_18

theorem weighted_00_03_03_18 : b4RawGapContribution ![0, 3, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 18] = b4GapPatternWeight 3 3 18 * 0 :=
      b4GapContribution_from_row 0 3 3 18 0 row_00_03_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_18

theorem row_00_03_03_19 : b4RowContribution (![0, 3, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 25 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 670 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 25^2 = 670
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_19

theorem weighted_00_03_03_19 : b4RawGapContribution ![0, 3, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 19] = b4GapPatternWeight 3 3 19 * 0 :=
      b4GapContribution_from_row 0 3 3 19 0 row_00_03_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_19

theorem row_00_03_03_20 : b4RowContribution (![0, 3, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 26 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 721 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 26^2 = 721
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_20

theorem weighted_00_03_03_20 : b4RawGapContribution ![0, 3, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 20] = b4GapPatternWeight 3 3 20 * 0 :=
      b4GapContribution_from_row 0 3 3 20 0 row_00_03_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_20

theorem row_00_03_03_21 : b4RowContribution (![0, 3, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 27 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 774 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 27^2 = 774
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_21

theorem weighted_00_03_03_21 : b4RawGapContribution ![0, 3, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 21] = b4GapPatternWeight 3 3 21 * 0 :=
      b4GapContribution_from_row 0 3 3 21 0 row_00_03_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_21

theorem row_00_03_03_22 : b4RowContribution (![0, 3, 6, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 6, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 6 + 28 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 6, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 829 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 6^2 + 28^2 = 829
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_03_22

theorem weighted_00_03_03_22 : b4RawGapContribution ![0, 3, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 3, 22] = b4GapPatternWeight 3 3 22 * 0 :=
      b4GapContribution_from_row 0 3 3 22 0 row_00_03_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_03_22

def dvalues_00_03_03 : Fin 23 → ℕ := ![0, 0, 0, 0, 0, 600, 24, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_03

theorem dblock_00_03_03 : b4GapPatternDBlock 0 3 3 = 1224 := by
  calc
    b4GapPatternDBlock 0 3 3 = ∑ d : Fin 23, dvalues_00_03_03 d := by
      apply b4GapDBlock_of_rows 0 3 3 dvalues_00_03_03
      intro d
      fin_cases d
      · exact weighted_00_03_03_00
      · exact weighted_00_03_03_01
      · exact weighted_00_03_03_02
      · exact weighted_00_03_03_03
      · exact weighted_00_03_03_04
      · exact weighted_00_03_03_05
      · exact weighted_00_03_03_06
      · exact weighted_00_03_03_07
      · exact weighted_00_03_03_08
      · exact weighted_00_03_03_09
      · exact weighted_00_03_03_10
      · exact weighted_00_03_03_11
      · exact weighted_00_03_03_12
      · exact weighted_00_03_03_13
      · exact weighted_00_03_03_14
      · exact weighted_00_03_03_15
      · exact weighted_00_03_03_16
      · exact weighted_00_03_03_17
      · exact weighted_00_03_03_18
      · exact weighted_00_03_03_19
      · exact weighted_00_03_03_20
      · exact weighted_00_03_03_21
      · exact weighted_00_03_03_22
    _ = 1224 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_03

end Paper7MomentGapNumeric
