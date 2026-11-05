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

def layers_01_00_08_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 38, 36, 32, 28, 24, 20, 16, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_08_00

theorem cells_01_00_08_00 : QTableValid (![1, 1, 9, 9] : Fin 4 → ℕ) layers_01_00_08_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_08_00

theorem valid_01_00_08_00 :
    SparseRowValid (![1, 1, 9, 9] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_00_08_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 9, 9] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 9 + 9 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 9^2 + 9^2 = 164
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_08_00
#print axioms Paper7MomentGapNumeric.valid_01_00_08_00

def qvalues_01_00_08_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_08_00

theorem row_01_00_08_00 : b4RowContribution (![1, 1, 9, 9] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_01_00_08_00) :=
      sparseRow_sound (![1, 1, 9, 9] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_00_08_00) valid_01_00_08_00
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_08_00 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_08_00

theorem weighted_01_00_08_00 : b4RawGapContribution ![1, 0, 8, 0] = 144 := by
  calc
    b4RawGapContribution ![1, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 24 :=
      b4GapContribution_from_row 1 0 8 0 24 row_01_00_08_00
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_00

theorem row_01_00_08_01 : b4RowContribution (![1, 1, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 10 = 21
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 10^2 = 183
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_01

theorem weighted_01_00_08_01 : b4RawGapContribution ![1, 0, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 0 :=
      b4GapContribution_from_row 1 0 8 1 0 row_01_00_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_01

theorem row_01_00_08_02 : b4RowContribution (![1, 1, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 11 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 11^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_02

theorem weighted_01_00_08_02 : b4RawGapContribution ![1, 0, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 2] = b4GapPatternWeight 0 8 2 * 0 :=
      b4GapContribution_from_row 1 0 8 2 0 row_01_00_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_02

def layers_01_00_08_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 39, 40, 40, 39, 36, 32, 28, 24, 20]]
#print axioms Paper7MomentGapNumeric.layers_01_00_08_03

theorem cells_01_00_08_03 : QTableValid (![1, 1, 9, 12] : Fin 4 → ℕ) layers_01_00_08_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_08_03

theorem valid_01_00_08_03 :
    SparseRowValid (![1, 1, 9, 12] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_08_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 9, 12] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 9 + 12 = 23
      decide
    have hzsq : (∑ i, (((![1, 1, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 9^2 + 12^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_08_03
#print axioms Paper7MomentGapNumeric.valid_01_00_08_03

def qvalues_01_00_08_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_08_03

theorem row_01_00_08_03 : b4RowContribution (![1, 1, 9, 12] : Fin 4 → ℕ) = 68 := by
  calc
    b4RowContribution (![1, 1, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_08_03) :=
      sparseRow_sound (![1, 1, 9, 12] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_08_03) valid_01_00_08_03
    _ = 68 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_08_03 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 68 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_08_03

theorem weighted_01_00_08_03 : b4RawGapContribution ![1, 0, 8, 3] = 816 := by
  calc
    b4RawGapContribution ![1, 0, 8, 3] = b4GapPatternWeight 0 8 3 * 68 :=
      b4GapContribution_from_row 1 0 8 3 68 row_01_00_08_03
    _ = 816 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_03

theorem row_01_00_08_04 : b4RowContribution (![1, 1, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 13] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 13 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 13^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_04

theorem weighted_01_00_08_04 : b4RawGapContribution ![1, 0, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 4] = b4GapPatternWeight 0 8 4 * 0 :=
      b4GapContribution_from_row 1 0 8 4 0 row_01_00_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_04

def layers_01_00_08_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 39, 40, 40, 40, 40, 39, 36, 32, 28]]
#print axioms Paper7MomentGapNumeric.layers_01_00_08_05

theorem cells_01_00_08_05 : QTableValid (![1, 1, 9, 14] : Fin 4 → ℕ) layers_01_00_08_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_08_05

theorem valid_01_00_08_05 :
    SparseRowValid (![1, 1, 9, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_08_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 9, 14] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 9 + 14 = 25
      decide
    have hzsq : (∑ i, (((![1, 1, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 9^2 + 14^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_08_05
#print axioms Paper7MomentGapNumeric.valid_01_00_08_05

def qvalues_01_00_08_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_08_05

theorem row_01_00_08_05 : b4RowContribution (![1, 1, 9, 14] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![1, 1, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_08_05) :=
      sparseRow_sound (![1, 1, 9, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_08_05) valid_01_00_08_05
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_08_05 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_08_05

theorem weighted_01_00_08_05 : b4RawGapContribution ![1, 0, 8, 5] = 432 := by
  calc
    b4RawGapContribution ![1, 0, 8, 5] = b4GapPatternWeight 0 8 5 * 36 :=
      b4GapContribution_from_row 1 0 8 5 36 row_01_00_08_05
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_05

theorem row_01_00_08_06 : b4RowContribution (![1, 1, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 15 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 15^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_06

theorem weighted_01_00_08_06 : b4RawGapContribution ![1, 0, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 6] = b4GapPatternWeight 0 8 6 * 0 :=
      b4GapContribution_from_row 1 0 8 6 0 row_01_00_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_06

theorem row_01_00_08_07 : b4RowContribution (![1, 1, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 16 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 16^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_07

theorem weighted_01_00_08_07 : b4RawGapContribution ![1, 0, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 7] = b4GapPatternWeight 0 8 7 * 0 :=
      b4GapContribution_from_row 1 0 8 7 0 row_01_00_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_07

theorem row_01_00_08_08 : b4RowContribution (![1, 1, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 17 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 17^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_08

theorem weighted_01_00_08_08 : b4RawGapContribution ![1, 0, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 8] = b4GapPatternWeight 0 8 8 * 0 :=
      b4GapContribution_from_row 1 0 8 8 0 row_01_00_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_08

theorem row_01_00_08_09 : b4RowContribution (![1, 1, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 18 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 407 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 18^2 = 407
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_09

theorem weighted_01_00_08_09 : b4RawGapContribution ![1, 0, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 9] = b4GapPatternWeight 0 8 9 * 0 :=
      b4GapContribution_from_row 1 0 8 9 0 row_01_00_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_09

theorem row_01_00_08_10 : b4RowContribution (![1, 1, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 19 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 19^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_10

theorem weighted_01_00_08_10 : b4RawGapContribution ![1, 0, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 10] = b4GapPatternWeight 0 8 10 * 0 :=
      b4GapContribution_from_row 1 0 8 10 0 row_01_00_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_10

theorem row_01_00_08_11 : b4RowContribution (![1, 1, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 20 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 20^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_11

theorem weighted_01_00_08_11 : b4RawGapContribution ![1, 0, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 11] = b4GapPatternWeight 0 8 11 * 0 :=
      b4GapContribution_from_row 1 0 8 11 0 row_01_00_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_11

theorem row_01_00_08_12 : b4RowContribution (![1, 1, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 21 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 524 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 21^2 = 524
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_12

theorem weighted_01_00_08_12 : b4RawGapContribution ![1, 0, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 12] = b4GapPatternWeight 0 8 12 * 0 :=
      b4GapContribution_from_row 1 0 8 12 0 row_01_00_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_12

def layers_01_00_08_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 39, 40, 40, 40, 40, 40, 40, 40, 40]]
#print axioms Paper7MomentGapNumeric.layers_01_00_08_13

theorem cells_01_00_08_13 : QTableValid (![1, 1, 9, 22] : Fin 4 → ℕ) layers_01_00_08_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_08_13

theorem valid_01_00_08_13 :
    SparseRowValid (![1, 1, 9, 22] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_00_08_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 9, 22] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 9 + 22 = 33
      decide
    have hzsq : (∑ i, (((![1, 1, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 567 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 9^2 + 22^2 = 567
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_08_13
#print axioms Paper7MomentGapNumeric.valid_01_00_08_13

def qvalues_01_00_08_13 : Fin 19 → ℕ := ![0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_08_13

theorem row_01_00_08_13 : b4RowContribution (![1, 1, 9, 22] : Fin 4 → ℕ) = 12 := by
  calc
    b4RowContribution (![1, 1, 9, 22] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_00_08_13) :=
      sparseRow_sound (![1, 1, 9, 22] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_00_08_13) valid_01_00_08_13
    _ = 12 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_08_13 Q := by
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
        _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_08_13

theorem weighted_01_00_08_13 : b4RawGapContribution ![1, 0, 8, 13] = 144 := by
  calc
    b4RawGapContribution ![1, 0, 8, 13] = b4GapPatternWeight 0 8 13 * 12 :=
      b4GapContribution_from_row 1 0 8 13 12 row_01_00_08_13
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_13

theorem row_01_00_08_14 : b4RowContribution (![1, 1, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 23 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 612 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 23^2 = 612
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_14

theorem weighted_01_00_08_14 : b4RawGapContribution ![1, 0, 8, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 14] = b4GapPatternWeight 0 8 14 * 0 :=
      b4GapContribution_from_row 1 0 8 14 0 row_01_00_08_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_14

theorem row_01_00_08_15 : b4RowContribution (![1, 1, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 24 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 659 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 24^2 = 659
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_15

theorem weighted_01_00_08_15 : b4RawGapContribution ![1, 0, 8, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 15] = b4GapPatternWeight 0 8 15 * 0 :=
      b4GapContribution_from_row 1 0 8 15 0 row_01_00_08_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_15

theorem row_01_00_08_16 : b4RowContribution (![1, 1, 9, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 25 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 708 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 25^2 = 708
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_16

theorem weighted_01_00_08_16 : b4RawGapContribution ![1, 0, 8, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 16] = b4GapPatternWeight 0 8 16 * 0 :=
      b4GapContribution_from_row 1 0 8 16 0 row_01_00_08_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_16

theorem row_01_00_08_17 : b4RowContribution (![1, 1, 9, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 9, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 9 + 26 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 9, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 759 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 9^2 + 26^2 = 759
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_08_17

theorem weighted_01_00_08_17 : b4RawGapContribution ![1, 0, 8, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 8, 17] = b4GapPatternWeight 0 8 17 * 0 :=
      b4GapContribution_from_row 1 0 8 17 0 row_01_00_08_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_08_17

def dvalues_01_00_08 : Fin 18 → ℕ := ![144, 0, 0, 816, 0, 432, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_08

theorem dblock_01_00_08 : b4GapPatternDBlock 1 0 8 = 1536 := by
  calc
    b4GapPatternDBlock 1 0 8 = ∑ d : Fin 18, dvalues_01_00_08 d := by
      apply b4GapDBlock_of_rows 1 0 8 dvalues_01_00_08
      intro d
      fin_cases d
      · exact weighted_01_00_08_00
      · exact weighted_01_00_08_01
      · exact weighted_01_00_08_02
      · exact weighted_01_00_08_03
      · exact weighted_01_00_08_04
      · exact weighted_01_00_08_05
      · exact weighted_01_00_08_06
      · exact weighted_01_00_08_07
      · exact weighted_01_00_08_08
      · exact weighted_01_00_08_09
      · exact weighted_01_00_08_10
      · exact weighted_01_00_08_11
      · exact weighted_01_00_08_12
      · exact weighted_01_00_08_13
      · exact weighted_01_00_08_14
      · exact weighted_01_00_08_15
      · exact weighted_01_00_08_16
      · exact weighted_01_00_08_17
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_08

end Paper7MomentGapNumeric
