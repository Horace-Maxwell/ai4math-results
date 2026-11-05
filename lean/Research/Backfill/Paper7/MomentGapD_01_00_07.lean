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

theorem row_01_00_07_00 : b4RowContribution (![1, 1, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 8 = 18
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 8^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_00

theorem weighted_01_00_07_00 : b4RawGapContribution ![1, 0, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 0] = b4GapPatternWeight 0 7 0 * 0 :=
      b4GapContribution_from_row 1 0 7 0 0 row_01_00_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_00

theorem row_01_00_07_01 : b4RowContribution (![1, 1, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 9 = 19
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 147 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 9^2 = 147
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_01

theorem weighted_01_00_07_01 : b4RawGapContribution ![1, 0, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 1] = b4GapPatternWeight 0 7 1 * 0 :=
      b4GapContribution_from_row 1 0 7 1 0 row_01_00_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_01

def layers_01_00_07_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 35, 36, 35, 32, 28, 24, 20, 16, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_07_02

theorem cells_01_00_07_02 : QTableValid (![1, 1, 8, 10] : Fin 4 → ℕ) layers_01_00_07_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_07_02

theorem valid_01_00_07_02 :
    SparseRowValid (![1, 1, 8, 10] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_07_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 8, 10] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 8 + 10 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 8^2 + 10^2 = 166
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_07_02
#print axioms Paper7MomentGapNumeric.valid_01_00_07_02

def qvalues_01_00_07_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_07_02

theorem row_01_00_07_02 : b4RowContribution (![1, 1, 8, 10] : Fin 4 → ℕ) = 28 := by
  calc
    b4RowContribution (![1, 1, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_01_00_07_02) :=
      sparseRow_sound (![1, 1, 8, 10] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_07_02) valid_01_00_07_02
    _ = 28 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_07_02 Q := by
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
        _ = 28 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_07_02

theorem weighted_01_00_07_02 : b4RawGapContribution ![1, 0, 7, 2] = 336 := by
  calc
    b4RawGapContribution ![1, 0, 7, 2] = b4GapPatternWeight 0 7 2 * 28 :=
      b4GapContribution_from_row 1 0 7 2 28 row_01_00_07_02
    _ = 336 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_02

def layers_01_00_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 35, 36, 36, 35, 32, 28, 24, 20, 16, 12]]
#print axioms Paper7MomentGapNumeric.layers_01_00_07_03

theorem cells_01_00_07_03 : QTableValid (![1, 1, 8, 11] : Fin 4 → ℕ) layers_01_00_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_07_03

theorem valid_01_00_07_03 :
    SparseRowValid (![1, 1, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_00_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 8, 11] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 8 + 11 = 21
      decide
    have hzsq : (∑ i, (((![1, 1, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 8^2 + 11^2 = 187
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_07_03
#print axioms Paper7MomentGapNumeric.valid_01_00_07_03

def qvalues_01_00_07_03 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_07_03

theorem row_01_00_07_03 : b4RowContribution (![1, 1, 8, 11] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 1, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_00_07_03) :=
      sparseRow_sound (![1, 1, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_00_07_03) valid_01_00_07_03
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_07_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_07_03

theorem weighted_01_00_07_03 : b4RawGapContribution ![1, 0, 7, 3] = 48 := by
  calc
    b4RawGapContribution ![1, 0, 7, 3] = b4GapPatternWeight 0 7 3 * 4 :=
      b4GapContribution_from_row 1 0 7 3 4 row_01_00_07_03
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_03

theorem row_01_00_07_04 : b4RowContribution (![1, 1, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 12 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 12^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_04

theorem weighted_01_00_07_04 : b4RawGapContribution ![1, 0, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 4] = b4GapPatternWeight 0 7 4 * 0 :=
      b4GapContribution_from_row 1 0 7 4 0 row_01_00_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_04

def layers_01_00_07_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 35, 36, 36, 36, 36, 35, 32, 28, 24, 20]]
#print axioms Paper7MomentGapNumeric.layers_01_00_07_05

theorem cells_01_00_07_05 : QTableValid (![1, 1, 8, 13] : Fin 4 → ℕ) layers_01_00_07_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_07_05

theorem valid_01_00_07_05 :
    SparseRowValid (![1, 1, 8, 13] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_01_00_07_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 8, 13] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 8 + 13 = 23
      decide
    have hzsq : (∑ i, (((![1, 1, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 8^2 + 13^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_07_05
#print axioms Paper7MomentGapNumeric.valid_01_00_07_05

def qvalues_01_00_07_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_07_05

theorem row_01_00_07_05 : b4RowContribution (![1, 1, 8, 13] : Fin 4 → ℕ) = 52 := by
  calc
    b4RowContribution (![1, 1, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10} : Finset (Fin 19)) (fun _ => layers_01_00_07_05) :=
      sparseRow_sound (![1, 1, 8, 13] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_01_00_07_05) valid_01_00_07_05
    _ = 52 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_07_05 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 52 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_07_05

theorem weighted_01_00_07_05 : b4RawGapContribution ![1, 0, 7, 5] = 624 := by
  calc
    b4RawGapContribution ![1, 0, 7, 5] = b4GapPatternWeight 0 7 5 * 52 :=
      b4GapContribution_from_row 1 0 7 5 52 row_01_00_07_05
    _ = 624 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_05

theorem row_01_00_07_06 : b4RowContribution (![1, 1, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 14] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 14 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 14^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_06

theorem weighted_01_00_07_06 : b4RawGapContribution ![1, 0, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 6] = b4GapPatternWeight 0 7 6 * 0 :=
      b4GapContribution_from_row 1 0 7 6 0 row_01_00_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_06

def layers_01_00_07_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 35, 36, 36, 36, 36, 36, 36, 35, 32, 28]]
#print axioms Paper7MomentGapNumeric.layers_01_00_07_07

theorem cells_01_00_07_07 : QTableValid (![1, 1, 8, 15] : Fin 4 → ℕ) layers_01_00_07_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_07_07

theorem valid_01_00_07_07 :
    SparseRowValid (![1, 1, 8, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_07_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 8, 15] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 8 + 15 = 25
      decide
    have hzsq : (∑ i, (((![1, 1, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 8^2 + 15^2 = 291
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_07_07
#print axioms Paper7MomentGapNumeric.valid_01_00_07_07

def qvalues_01_00_07_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_07_07

theorem row_01_00_07_07 : b4RowContribution (![1, 1, 8, 15] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![1, 1, 8, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_07_07) :=
      sparseRow_sound (![1, 1, 8, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_07_07) valid_01_00_07_07
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_07_07 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_07_07

theorem weighted_01_00_07_07 : b4RawGapContribution ![1, 0, 7, 7] = 420 := by
  calc
    b4RawGapContribution ![1, 0, 7, 7] = b4GapPatternWeight 0 7 7 * 35 :=
      b4GapContribution_from_row 1 0 7 7 35 row_01_00_07_07
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_07

theorem row_01_00_07_08 : b4RowContribution (![1, 1, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 16 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 16^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_08

theorem weighted_01_00_07_08 : b4RawGapContribution ![1, 0, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 8] = b4GapPatternWeight 0 7 8 * 0 :=
      b4GapContribution_from_row 1 0 7 8 0 row_01_00_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_08

theorem row_01_00_07_09 : b4RowContribution (![1, 1, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 17 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 17^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_09

theorem weighted_01_00_07_09 : b4RawGapContribution ![1, 0, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 9] = b4GapPatternWeight 0 7 9 * 0 :=
      b4GapContribution_from_row 1 0 7 9 0 row_01_00_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_09

theorem row_01_00_07_10 : b4RowContribution (![1, 1, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 18 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 18^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_10

theorem weighted_01_00_07_10 : b4RawGapContribution ![1, 0, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 10] = b4GapPatternWeight 0 7 10 * 0 :=
      b4GapContribution_from_row 1 0 7 10 0 row_01_00_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_10

theorem row_01_00_07_11 : b4RowContribution (![1, 1, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 19 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 19^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_11

theorem weighted_01_00_07_11 : b4RawGapContribution ![1, 0, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 11] = b4GapPatternWeight 0 7 11 * 0 :=
      b4GapContribution_from_row 1 0 7 11 0 row_01_00_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_11

theorem row_01_00_07_12 : b4RowContribution (![1, 1, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 20 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 466 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 20^2 = 466
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_12

theorem weighted_01_00_07_12 : b4RawGapContribution ![1, 0, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 12] = b4GapPatternWeight 0 7 12 * 0 :=
      b4GapContribution_from_row 1 0 7 12 0 row_01_00_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_12

theorem row_01_00_07_13 : b4RowContribution (![1, 1, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 21 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 21^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_13

theorem weighted_01_00_07_13 : b4RawGapContribution ![1, 0, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 13] = b4GapPatternWeight 0 7 13 * 0 :=
      b4GapContribution_from_row 1 0 7 13 0 row_01_00_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_13

theorem row_01_00_07_14 : b4RowContribution (![1, 1, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 22 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 22^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_14

theorem weighted_01_00_07_14 : b4RawGapContribution ![1, 0, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 14] = b4GapPatternWeight 0 7 14 * 0 :=
      b4GapContribution_from_row 1 0 7 14 0 row_01_00_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_14

theorem row_01_00_07_15 : b4RowContribution (![1, 1, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 23 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 595 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 23^2 = 595
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_15

theorem weighted_01_00_07_15 : b4RawGapContribution ![1, 0, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 15] = b4GapPatternWeight 0 7 15 * 0 :=
      b4GapContribution_from_row 1 0 7 15 0 row_01_00_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_15

theorem row_01_00_07_16 : b4RowContribution (![1, 1, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 24 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 642 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 24^2 = 642
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_16

theorem weighted_01_00_07_16 : b4RawGapContribution ![1, 0, 7, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 16] = b4GapPatternWeight 0 7 16 * 0 :=
      b4GapContribution_from_row 1 0 7 16 0 row_01_00_07_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_16

theorem row_01_00_07_17 : b4RowContribution (![1, 1, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 25 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 691 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 25^2 = 691
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_17

theorem weighted_01_00_07_17 : b4RawGapContribution ![1, 0, 7, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 17] = b4GapPatternWeight 0 7 17 * 0 :=
      b4GapContribution_from_row 1 0 7 17 0 row_01_00_07_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_17

theorem row_01_00_07_18 : b4RowContribution (![1, 1, 8, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 26 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 742 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 26^2 = 742
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_18

theorem weighted_01_00_07_18 : b4RawGapContribution ![1, 0, 7, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 18] = b4GapPatternWeight 0 7 18 * 0 :=
      b4GapContribution_from_row 1 0 7 18 0 row_01_00_07_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_18

theorem row_01_00_07_19 : b4RowContribution (![1, 1, 8, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 8, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 8 + 27 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 8, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 795 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 8^2 + 27^2 = 795
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_07_19

theorem weighted_01_00_07_19 : b4RawGapContribution ![1, 0, 7, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 7, 19] = b4GapPatternWeight 0 7 19 * 0 :=
      b4GapContribution_from_row 1 0 7 19 0 row_01_00_07_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_07_19

def dvalues_01_00_07 : Fin 20 → ℕ := ![0, 0, 336, 48, 0, 624, 0, 420, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_07

theorem dblock_01_00_07 : b4GapPatternDBlock 1 0 7 = 1428 := by
  calc
    b4GapPatternDBlock 1 0 7 = ∑ d : Fin 20, dvalues_01_00_07 d := by
      apply b4GapDBlock_of_rows 1 0 7 dvalues_01_00_07
      intro d
      fin_cases d
      · exact weighted_01_00_07_00
      · exact weighted_01_00_07_01
      · exact weighted_01_00_07_02
      · exact weighted_01_00_07_03
      · exact weighted_01_00_07_04
      · exact weighted_01_00_07_05
      · exact weighted_01_00_07_06
      · exact weighted_01_00_07_07
      · exact weighted_01_00_07_08
      · exact weighted_01_00_07_09
      · exact weighted_01_00_07_10
      · exact weighted_01_00_07_11
      · exact weighted_01_00_07_12
      · exact weighted_01_00_07_13
      · exact weighted_01_00_07_14
      · exact weighted_01_00_07_15
      · exact weighted_01_00_07_16
      · exact weighted_01_00_07_17
      · exact weighted_01_00_07_18
      · exact weighted_01_00_07_19
    _ = 1428 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_07

end Paper7MomentGapNumeric
