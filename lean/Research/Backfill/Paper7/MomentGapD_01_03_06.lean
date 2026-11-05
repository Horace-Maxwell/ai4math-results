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

def layers_01_03_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 75, 85, 93, 97, 97, 93, 85, 75, 65, 55]]
#print axioms Paper7MomentGapNumeric.layers_01_03_06_00

theorem cells_01_03_06_00 : QTableValid (![1, 4, 10, 10] : Fin 4 → ℕ) layers_01_03_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_06_00

theorem valid_01_03_06_00 :
    SparseRowValid (![1, 4, 10, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_03_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 10, 10] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 10 + 10 = 25
      decide
    have hzsq : (∑ i, (((![1, 4, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 10^2 + 10^2 = 217
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_06_00
#print axioms Paper7MomentGapNumeric.valid_01_03_06_00

def qvalues_01_03_06_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_06_00

theorem row_01_03_06_00 : b4RowContribution (![1, 4, 10, 10] : Fin 4 → ℕ) = 85 := by
  calc
    b4RowContribution (![1, 4, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_03_06_00) :=
      sparseRow_sound (![1, 4, 10, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_03_06_00) valid_01_03_06_00
    _ = 85 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_06_00 Q := by
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
        _ = 85 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_06_00

theorem weighted_01_03_06_00 : b4RawGapContribution ![1, 3, 6, 0] = 1020 := by
  calc
    b4RawGapContribution ![1, 3, 6, 0] = b4GapPatternWeight 3 6 0 * 85 :=
      b4GapContribution_from_row 1 3 6 0 85 row_01_03_06_00
    _ = 1020 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_00

def layers_01_03_06_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 75, 85, 94, 100, 102, 100, 94, 85, 75, 65]]
#print axioms Paper7MomentGapNumeric.layers_01_03_06_01

theorem cells_01_03_06_01 : QTableValid (![1, 4, 10, 11] : Fin 4 → ℕ) layers_01_03_06_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_06_01

theorem valid_01_03_06_01 :
    SparseRowValid (![1, 4, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_03_06_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 10, 11] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 10 + 11 = 26
      decide
    have hzsq : (∑ i, (((![1, 4, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 10^2 + 11^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_06_01
#print axioms Paper7MomentGapNumeric.valid_01_03_06_01

def qvalues_01_03_06_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_06_01

theorem row_01_03_06_01 : b4RowContribution (![1, 4, 10, 11] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![1, 4, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_01_03_06_01) :=
      sparseRow_sound (![1, 4, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_03_06_01) valid_01_03_06_01
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_06_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_06_01

theorem weighted_01_03_06_01 : b4RawGapContribution ![1, 3, 6, 1] = 600 := by
  calc
    b4RawGapContribution ![1, 3, 6, 1] = b4GapPatternWeight 3 6 1 * 25 :=
      b4GapContribution_from_row 1 3 6 1 25 row_01_03_06_01
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_01

theorem row_01_03_06_02 : b4RowContribution (![1, 4, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 12 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 12^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_02

theorem weighted_01_03_06_02 : b4RawGapContribution ![1, 3, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 2] = b4GapPatternWeight 3 6 2 * 0 :=
      b4GapContribution_from_row 1 3 6 2 0 row_01_03_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_02

def layers_01_03_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 75, 85, 94, 101, 106, 108, 106, 101, 94, 85]]
#print axioms Paper7MomentGapNumeric.layers_01_03_06_03

theorem cells_01_03_06_03 : QTableValid (![1, 4, 10, 13] : Fin 4 → ℕ) layers_01_03_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_06_03

theorem valid_01_03_06_03 :
    SparseRowValid (![1, 4, 10, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_03_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 10, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 10 + 13 = 28
      decide
    have hzsq : (∑ i, (((![1, 4, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 10^2 + 13^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_06_03
#print axioms Paper7MomentGapNumeric.valid_01_03_06_03

def qvalues_01_03_06_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_06_03

theorem row_01_03_06_03 : b4RowContribution (![1, 4, 10, 13] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![1, 4, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_03_06_03) :=
      sparseRow_sound (![1, 4, 10, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_03_06_03) valid_01_03_06_03
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_06_03 Q := by
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
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_06_03

theorem weighted_01_03_06_03 : b4RawGapContribution ![1, 3, 6, 3] = 1320 := by
  calc
    b4RawGapContribution ![1, 3, 6, 3] = b4GapPatternWeight 3 6 3 * 55 :=
      b4GapContribution_from_row 1 3 6 3 55 row_01_03_06_03
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_03

theorem row_01_03_06_04 : b4RowContribution (![1, 4, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 14^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_04

theorem weighted_01_03_06_04 : b4RawGapContribution ![1, 3, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 4] = b4GapPatternWeight 3 6 4 * 0 :=
      b4GapContribution_from_row 1 3 6 4 0 row_01_03_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_04

theorem row_01_03_06_05 : b4RowContribution (![1, 4, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 15^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_05

theorem weighted_01_03_06_05 : b4RawGapContribution ![1, 3, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 5] = b4GapPatternWeight 3 6 5 * 0 :=
      b4GapContribution_from_row 1 3 6 5 0 row_01_03_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_05

theorem row_01_03_06_06 : b4RowContribution (![1, 4, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 16^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_06

theorem weighted_01_03_06_06 : b4RawGapContribution ![1, 3, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 6] = b4GapPatternWeight 3 6 6 * 0 :=
      b4GapContribution_from_row 1 3 6 6 0 row_01_03_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_06

theorem row_01_03_06_07 : b4RowContribution (![1, 4, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 17^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_07

theorem weighted_01_03_06_07 : b4RawGapContribution ![1, 3, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 7] = b4GapPatternWeight 3 6 7 * 0 :=
      b4GapContribution_from_row 1 3 6 7 0 row_01_03_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_07

theorem row_01_03_06_08 : b4RowContribution (![1, 4, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 18^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_08

theorem weighted_01_03_06_08 : b4RawGapContribution ![1, 3, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 8] = b4GapPatternWeight 3 6 8 * 0 :=
      b4GapContribution_from_row 1 3 6 8 0 row_01_03_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_08

theorem row_01_03_06_09 : b4RowContribution (![1, 4, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 478 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 19^2 = 478
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_09

theorem weighted_01_03_06_09 : b4RawGapContribution ![1, 3, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 9] = b4GapPatternWeight 3 6 9 * 0 :=
      b4GapContribution_from_row 1 3 6 9 0 row_01_03_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_09

theorem row_01_03_06_10 : b4RowContribution (![1, 4, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 20^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_10

theorem weighted_01_03_06_10 : b4RawGapContribution ![1, 3, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 10] = b4GapPatternWeight 3 6 10 * 0 :=
      b4GapContribution_from_row 1 3 6 10 0 row_01_03_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_10

theorem row_01_03_06_11 : b4RowContribution (![1, 4, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 21^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_11

theorem weighted_01_03_06_11 : b4RawGapContribution ![1, 3, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 11] = b4GapPatternWeight 3 6 11 * 0 :=
      b4GapContribution_from_row 1 3 6 11 0 row_01_03_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_11

theorem row_01_03_06_12 : b4RowContribution (![1, 4, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 10, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 10 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 601 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 10^2 + 22^2 = 601
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_06_12

theorem weighted_01_03_06_12 : b4RawGapContribution ![1, 3, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 6, 12] = b4GapPatternWeight 3 6 12 * 0 :=
      b4GapContribution_from_row 1 3 6 12 0 row_01_03_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_06_12

def dvalues_01_03_06 : Fin 13 → ℕ := ![1020, 600, 0, 1320, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_06

theorem dblock_01_03_06 : b4GapPatternDBlock 1 3 6 = 2940 := by
  calc
    b4GapPatternDBlock 1 3 6 = ∑ d : Fin 13, dvalues_01_03_06 d := by
      apply b4GapDBlock_of_rows 1 3 6 dvalues_01_03_06
      intro d
      fin_cases d
      · exact weighted_01_03_06_00
      · exact weighted_01_03_06_01
      · exact weighted_01_03_06_02
      · exact weighted_01_03_06_03
      · exact weighted_01_03_06_04
      · exact weighted_01_03_06_05
      · exact weighted_01_03_06_06
      · exact weighted_01_03_06_07
      · exact weighted_01_03_06_08
      · exact weighted_01_03_06_09
      · exact weighted_01_03_06_10
      · exact weighted_01_03_06_11
      · exact weighted_01_03_06_12
    _ = 2940 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_06

end Paper7MomentGapNumeric
