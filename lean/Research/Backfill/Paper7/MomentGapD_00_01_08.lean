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

def layers_00_01_08_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 19, 17, 15, 13, 11, 9, 7, 5, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_08_00

theorem cells_00_01_08_00 : QTableValid (![0, 1, 9, 9] : Fin 4 → ℕ) layers_00_01_08_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_08_00

theorem valid_00_01_08_00 :
    SparseRowValid (![0, 1, 9, 9] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_00_01_08_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 9, 9] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 9 + 9 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 9^2 + 9^2 = 163
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_08_00
#print axioms Paper7MomentGapNumeric.valid_00_01_08_00

def qvalues_00_01_08_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_08_00

theorem row_00_01_08_00 : b4RowContribution (![0, 1, 9, 9] : Fin 4 → ℕ) = 7 := by
  calc
    b4RowContribution (![0, 1, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_00_01_08_00) :=
      sparseRow_sound (![0, 1, 9, 9] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_00_01_08_00) valid_00_01_08_00
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_08_00 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 7 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_08_00

theorem weighted_00_01_08_00 : b4RawGapContribution ![0, 1, 8, 0] = 84 := by
  calc
    b4RawGapContribution ![0, 1, 8, 0] = b4GapPatternWeight 1 8 0 * 7 :=
      b4GapContribution_from_row 0 1 8 0 7 row_00_01_08_00
    _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_00

def layers_00_01_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 20, 19, 17, 15, 13, 11, 9, 7, 5]]
#print axioms Paper7MomentGapNumeric.layers_00_01_08_01

theorem cells_00_01_08_01 : QTableValid (![0, 1, 9, 10] : Fin 4 → ℕ) layers_00_01_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_08_01

theorem valid_00_01_08_01 :
    SparseRowValid (![0, 1, 9, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 9, 10] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 9 + 10 = 20
      decide
    have hzsq : (∑ i, (((![0, 1, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 9^2 + 10^2 = 182
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_08_01
#print axioms Paper7MomentGapNumeric.valid_00_01_08_01

def qvalues_00_01_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_08_01

theorem row_00_01_08_01 : b4RowContribution (![0, 1, 9, 10] : Fin 4 → ℕ) = 11 := by
  calc
    b4RowContribution (![0, 1, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_01) :=
      sparseRow_sound (![0, 1, 9, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_01) valid_00_01_08_01
    _ = 11 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_08_01 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 11 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_08_01

theorem weighted_00_01_08_01 : b4RawGapContribution ![0, 1, 8, 1] = 264 := by
  calc
    b4RawGapContribution ![0, 1, 8, 1] = b4GapPatternWeight 1 8 1 * 11 :=
      b4GapContribution_from_row 0 1 8 1 11 row_00_01_08_01
    _ = 264 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_01

theorem row_00_01_08_02 : b4RowContribution (![0, 1, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 11 = 21
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 11^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_02

theorem weighted_00_01_08_02 : b4RawGapContribution ![0, 1, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 2] = b4GapPatternWeight 1 8 2 * 0 :=
      b4GapContribution_from_row 0 1 8 2 0 row_00_01_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_02

def layers_00_01_08_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 20, 20, 20, 19, 17, 15, 13, 11, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_01_08_03

theorem cells_00_01_08_03 : QTableValid (![0, 1, 9, 12] : Fin 4 → ℕ) layers_00_01_08_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_08_03

theorem valid_00_01_08_03 :
    SparseRowValid (![0, 1, 9, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_01_08_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 9, 12] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 9 + 12 = 22
      decide
    have hzsq : (∑ i, (((![0, 1, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 9^2 + 12^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_08_03
#print axioms Paper7MomentGapNumeric.valid_00_01_08_03

def qvalues_00_01_08_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_08_03

theorem row_00_01_08_03 : b4RowContribution (![0, 1, 9, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![0, 1, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_00_01_08_03) :=
      sparseRow_sound (![0, 1, 9, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_01_08_03) valid_00_01_08_03
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_08_03 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_08_03

theorem weighted_00_01_08_03 : b4RawGapContribution ![0, 1, 8, 3] = 480 := by
  calc
    b4RawGapContribution ![0, 1, 8, 3] = b4GapPatternWeight 1 8 3 * 20 :=
      b4GapContribution_from_row 0 1 8 3 20 row_00_01_08_03
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_03

theorem row_00_01_08_04 : b4RowContribution (![0, 1, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 13 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 13^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_04

theorem weighted_00_01_08_04 : b4RawGapContribution ![0, 1, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 4] = b4GapPatternWeight 1 8 4 * 0 :=
      b4GapContribution_from_row 0 1 8 4 0 row_00_01_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_04

def layers_00_01_08_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 20, 20, 20, 20, 20, 19, 17, 15, 13]]
#print axioms Paper7MomentGapNumeric.layers_00_01_08_05

theorem cells_00_01_08_05 : QTableValid (![0, 1, 9, 14] : Fin 4 → ℕ) layers_00_01_08_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_08_05

theorem valid_00_01_08_05 :
    SparseRowValid (![0, 1, 9, 14] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_08_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 9, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 9 + 14 = 24
      decide
    have hzsq : (∑ i, (((![0, 1, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 9^2 + 14^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_08_05
#print axioms Paper7MomentGapNumeric.valid_00_01_08_05

def qvalues_00_01_08_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_08_05

theorem row_00_01_08_05 : b4RowContribution (![0, 1, 9, 14] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![0, 1, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_01_08_05) :=
      sparseRow_sound (![0, 1, 9, 14] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_08_05) valid_00_01_08_05
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_08_05 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_08_05

theorem weighted_00_01_08_05 : b4RawGapContribution ![0, 1, 8, 5] = 480 := by
  calc
    b4RawGapContribution ![0, 1, 8, 5] = b4GapPatternWeight 1 8 5 * 20 :=
      b4GapContribution_from_row 0 1 8 5 20 row_00_01_08_05
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_05

theorem row_00_01_08_06 : b4RowContribution (![0, 1, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 15 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 15^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_06

theorem weighted_00_01_08_06 : b4RawGapContribution ![0, 1, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 6] = b4GapPatternWeight 1 8 6 * 0 :=
      b4GapContribution_from_row 0 1 8 6 0 row_00_01_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_06

theorem row_00_01_08_07 : b4RowContribution (![0, 1, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 16 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 16^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_07

theorem weighted_00_01_08_07 : b4RawGapContribution ![0, 1, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 7] = b4GapPatternWeight 1 8 7 * 0 :=
      b4GapContribution_from_row 0 1 8 7 0 row_00_01_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_07

theorem row_00_01_08_08 : b4RowContribution (![0, 1, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 17 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 17^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_08

theorem weighted_00_01_08_08 : b4RawGapContribution ![0, 1, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 8] = b4GapPatternWeight 1 8 8 * 0 :=
      b4GapContribution_from_row 0 1 8 8 0 row_00_01_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_08

theorem row_00_01_08_09 : b4RowContribution (![0, 1, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 18 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 18^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_09

theorem weighted_00_01_08_09 : b4RawGapContribution ![0, 1, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 9] = b4GapPatternWeight 1 8 9 * 0 :=
      b4GapContribution_from_row 0 1 8 9 0 row_00_01_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_09

theorem row_00_01_08_10 : b4RowContribution (![0, 1, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 19 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 19^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_10

theorem weighted_00_01_08_10 : b4RawGapContribution ![0, 1, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 10] = b4GapPatternWeight 1 8 10 * 0 :=
      b4GapContribution_from_row 0 1 8 10 0 row_00_01_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_10

theorem row_00_01_08_11 : b4RowContribution (![0, 1, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 20 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 20^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_11

theorem weighted_00_01_08_11 : b4RawGapContribution ![0, 1, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 11] = b4GapPatternWeight 1 8 11 * 0 :=
      b4GapContribution_from_row 0 1 8 11 0 row_00_01_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_11

theorem row_00_01_08_12 : b4RowContribution (![0, 1, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 21 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 523 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 21^2 = 523
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_12

theorem weighted_00_01_08_12 : b4RawGapContribution ![0, 1, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 12] = b4GapPatternWeight 1 8 12 * 0 :=
      b4GapContribution_from_row 0 1 8 12 0 row_00_01_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_12

def layers_00_01_08_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20]]
#print axioms Paper7MomentGapNumeric.layers_00_01_08_13

theorem cells_00_01_08_13 : QTableValid (![0, 1, 9, 22] : Fin 4 → ℕ) layers_00_01_08_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_08_13

theorem valid_00_01_08_13 :
    SparseRowValid (![0, 1, 9, 22] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 9, 22] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 9 + 22 = 32
      decide
    have hzsq : (∑ i, (((![0, 1, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 9^2 + 22^2 = 566
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_08_13
#print axioms Paper7MomentGapNumeric.valid_00_01_08_13

def qvalues_00_01_08_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_08_13

theorem row_00_01_08_13 : b4RowContribution (![0, 1, 9, 22] : Fin 4 → ℕ) = 11 := by
  calc
    b4RowContribution (![0, 1, 9, 22] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_13) :=
      sparseRow_sound (![0, 1, 9, 22] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_08_13) valid_00_01_08_13
    _ = 11 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_08_13 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 11 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_08_13

theorem weighted_00_01_08_13 : b4RawGapContribution ![0, 1, 8, 13] = 264 := by
  calc
    b4RawGapContribution ![0, 1, 8, 13] = b4GapPatternWeight 1 8 13 * 11 :=
      b4GapContribution_from_row 0 1 8 13 11 row_00_01_08_13
    _ = 264 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_13

theorem row_00_01_08_14 : b4RowContribution (![0, 1, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 23 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 611 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 23^2 = 611
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_14

theorem weighted_00_01_08_14 : b4RawGapContribution ![0, 1, 8, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 14] = b4GapPatternWeight 1 8 14 * 0 :=
      b4GapContribution_from_row 0 1 8 14 0 row_00_01_08_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_14

theorem row_00_01_08_15 : b4RowContribution (![0, 1, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 24 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 658 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 24^2 = 658
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_15

theorem weighted_00_01_08_15 : b4RawGapContribution ![0, 1, 8, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 15] = b4GapPatternWeight 1 8 15 * 0 :=
      b4GapContribution_from_row 0 1 8 15 0 row_00_01_08_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_15

theorem row_00_01_08_16 : b4RowContribution (![0, 1, 9, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 25 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 707 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 25^2 = 707
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_16

theorem weighted_00_01_08_16 : b4RawGapContribution ![0, 1, 8, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 16] = b4GapPatternWeight 1 8 16 * 0 :=
      b4GapContribution_from_row 0 1 8 16 0 row_00_01_08_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_16

theorem row_00_01_08_17 : b4RowContribution (![0, 1, 9, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 26 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 758 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 26^2 = 758
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_17

theorem weighted_00_01_08_17 : b4RawGapContribution ![0, 1, 8, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 17] = b4GapPatternWeight 1 8 17 * 0 :=
      b4GapContribution_from_row 0 1 8 17 0 row_00_01_08_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_17

theorem row_00_01_08_18 : b4RowContribution (![0, 1, 9, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 9, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 9 + 27 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 9, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 811 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 9^2 + 27^2 = 811
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_08_18

theorem weighted_00_01_08_18 : b4RawGapContribution ![0, 1, 8, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 8, 18] = b4GapPatternWeight 1 8 18 * 0 :=
      b4GapContribution_from_row 0 1 8 18 0 row_00_01_08_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_08_18

def dvalues_00_01_08 : Fin 19 → ℕ := ![84, 264, 0, 480, 0, 480, 0, 0, 0, 0, 0, 0, 0, 264, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_08

theorem dblock_00_01_08 : b4GapPatternDBlock 0 1 8 = 1572 := by
  calc
    b4GapPatternDBlock 0 1 8 = ∑ d : Fin 19, dvalues_00_01_08 d := by
      apply b4GapDBlock_of_rows 0 1 8 dvalues_00_01_08
      intro d
      fin_cases d
      · exact weighted_00_01_08_00
      · exact weighted_00_01_08_01
      · exact weighted_00_01_08_02
      · exact weighted_00_01_08_03
      · exact weighted_00_01_08_04
      · exact weighted_00_01_08_05
      · exact weighted_00_01_08_06
      · exact weighted_00_01_08_07
      · exact weighted_00_01_08_08
      · exact weighted_00_01_08_09
      · exact weighted_00_01_08_10
      · exact weighted_00_01_08_11
      · exact weighted_00_01_08_12
      · exact weighted_00_01_08_13
      · exact weighted_00_01_08_14
      · exact weighted_00_01_08_15
      · exact weighted_00_01_08_16
      · exact weighted_00_01_08_17
      · exact weighted_00_01_08_18
    _ = 1572 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_08

end Paper7MomentGapNumeric
