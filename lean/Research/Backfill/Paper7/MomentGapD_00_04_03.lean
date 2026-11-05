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

theorem row_00_04_03_00 : b4RowContribution (![0, 4, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 7 = 18
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 7^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_00

theorem weighted_00_04_03_00 : b4RawGapContribution ![0, 4, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 0] = b4GapPatternWeight 4 3 0 * 0 :=
      b4GapContribution_from_row 0 4 3 0 0 row_00_04_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_00

theorem row_00_04_03_01 : b4RowContribution (![0, 4, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 8 = 19
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 8^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_01

theorem weighted_00_04_03_01 : b4RawGapContribution ![0, 4, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 1] = b4GapPatternWeight 4 3 1 * 0 :=
      b4GapContribution_from_row 0 4 3 1 0 row_00_04_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_01

theorem row_00_04_03_02 : b4RowContribution (![0, 4, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 9 = 20
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 9^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_02

theorem weighted_00_04_03_02 : b4RawGapContribution ![0, 4, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 2] = b4GapPatternWeight 4 3 2 * 0 :=
      b4GapContribution_from_row 0 4 3 2 0 row_00_04_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_02

theorem row_00_04_03_03 : b4RowContribution (![0, 4, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 10 = 21
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 10^2 = 165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_03

theorem weighted_00_04_03_03 : b4RawGapContribution ![0, 4, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 3] = b4GapPatternWeight 4 3 3 * 0 :=
      b4GapContribution_from_row 0 4 3 3 0 row_00_04_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_03

def layers_00_04_03_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 34, 37, 39, 40, 39, 37, 34, 30, 25, 20, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_04_03_04

theorem cells_00_04_03_04 : QTableValid (![0, 4, 7, 11] : Fin 4 → ℕ) layers_00_04_03_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_03_04

theorem valid_00_04_03_04 :
    SparseRowValid (![0, 4, 7, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_04_03_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 7, 11] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 7 + 11 = 22
      decide
    have hzsq : (∑ i, (((![0, 4, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 7^2 + 11^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_03_04
#print axioms Paper7MomentGapNumeric.valid_00_04_03_04

def qvalues_00_04_03_04 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_03_04

theorem row_00_04_03_04 : b4RowContribution (![0, 4, 7, 11] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 4, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_00_04_03_04) :=
      sparseRow_sound (![0, 4, 7, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_04_03_04) valid_00_04_03_04
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_03_04 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_04_03_04

theorem weighted_00_04_03_04 : b4RawGapContribution ![0, 4, 3, 4] = 24 := by
  calc
    b4RawGapContribution ![0, 4, 3, 4] = b4GapPatternWeight 4 3 4 * 1 :=
      b4GapContribution_from_row 0 4 3 4 1 row_00_04_03_04
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_04

theorem row_00_04_03_05 : b4RowContribution (![0, 4, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 12 = 23
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 12^2 = 209
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_05

theorem weighted_00_04_03_05 : b4RawGapContribution ![0, 4, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 5] = b4GapPatternWeight 4 3 5 * 0 :=
      b4GapContribution_from_row 0 4 3 5 0 row_00_04_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_05

def layers_00_04_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 34, 37, 39, 40, 40, 40, 39, 37, 34, 30, 25]]
#print axioms Paper7MomentGapNumeric.layers_00_04_03_06

theorem cells_00_04_03_06 : QTableValid (![0, 4, 7, 13] : Fin 4 → ℕ) layers_00_04_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_03_06

theorem valid_00_04_03_06 :
    SparseRowValid (![0, 4, 7, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 7, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 7 + 13 = 24
      decide
    have hzsq : (∑ i, (((![0, 4, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 7^2 + 13^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_03_06
#print axioms Paper7MomentGapNumeric.valid_00_04_03_06

def qvalues_00_04_03_06 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_03_06

theorem row_00_04_03_06 : b4RowContribution (![0, 4, 7, 13] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![0, 4, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_03_06) :=
      sparseRow_sound (![0, 4, 7, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_03_06) valid_00_04_03_06
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_03_06 Q := by
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
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_03_06

theorem weighted_00_04_03_06 : b4RawGapContribution ![0, 4, 3, 6] = 1128 := by
  calc
    b4RawGapContribution ![0, 4, 3, 6] = b4GapPatternWeight 4 3 6 * 47 :=
      b4GapContribution_from_row 0 4 3 6 47 row_00_04_03_06
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_06

theorem row_00_04_03_07 : b4RowContribution (![0, 4, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 14 = 25
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 14^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_07

theorem weighted_00_04_03_07 : b4RawGapContribution ![0, 4, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 7] = b4GapPatternWeight 4 3 7 * 0 :=
      b4GapContribution_from_row 0 4 3 7 0 row_00_04_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_07

def layers_00_04_03_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 34, 37, 39, 40, 40, 40, 40, 40, 39, 37, 34]]
#print axioms Paper7MomentGapNumeric.layers_00_04_03_08

theorem cells_00_04_03_08 : QTableValid (![0, 4, 7, 15] : Fin 4 → ℕ) layers_00_04_03_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_03_08

theorem valid_00_04_03_08 :
    SparseRowValid (![0, 4, 7, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_03_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 7, 15] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 7 + 15 = 26
      decide
    have hzsq : (∑ i, (((![0, 4, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 7^2 + 15^2 = 290
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_03_08
#print axioms Paper7MomentGapNumeric.valid_00_04_03_08

def qvalues_00_04_03_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_03_08

theorem row_00_04_03_08 : b4RowContribution (![0, 4, 7, 15] : Fin 4 → ℕ) = 34 := by
  calc
    b4RowContribution (![0, 4, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_04_03_08) :=
      sparseRow_sound (![0, 4, 7, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_04_03_08) valid_00_04_03_08
    _ = 34 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_03_08 Q := by
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
        _ = 34 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_03_08

theorem weighted_00_04_03_08 : b4RawGapContribution ![0, 4, 3, 8] = 816 := by
  calc
    b4RawGapContribution ![0, 4, 3, 8] = b4GapPatternWeight 4 3 8 * 34 :=
      b4GapContribution_from_row 0 4 3 8 34 row_00_04_03_08
    _ = 816 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_08

theorem row_00_04_03_09 : b4RowContribution (![0, 4, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 16 = 27
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 16^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_09

theorem weighted_00_04_03_09 : b4RawGapContribution ![0, 4, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 9] = b4GapPatternWeight 4 3 9 * 0 :=
      b4GapContribution_from_row 0 4 3 9 0 row_00_04_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_09

theorem row_00_04_03_10 : b4RowContribution (![0, 4, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 17 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 17^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_10

theorem weighted_00_04_03_10 : b4RawGapContribution ![0, 4, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 10] = b4GapPatternWeight 4 3 10 * 0 :=
      b4GapContribution_from_row 0 4 3 10 0 row_00_04_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_10

theorem row_00_04_03_11 : b4RowContribution (![0, 4, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 18 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 18^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_11

theorem weighted_00_04_03_11 : b4RawGapContribution ![0, 4, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 11] = b4GapPatternWeight 4 3 11 * 0 :=
      b4GapContribution_from_row 0 4 3 11 0 row_00_04_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_11

theorem row_00_04_03_12 : b4RowContribution (![0, 4, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 19 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 19^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_12

theorem weighted_00_04_03_12 : b4RawGapContribution ![0, 4, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 12] = b4GapPatternWeight 4 3 12 * 0 :=
      b4GapContribution_from_row 0 4 3 12 0 row_00_04_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_12

theorem row_00_04_03_13 : b4RowContribution (![0, 4, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 20 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 20^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_13

theorem weighted_00_04_03_13 : b4RawGapContribution ![0, 4, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 13] = b4GapPatternWeight 4 3 13 * 0 :=
      b4GapContribution_from_row 0 4 3 13 0 row_00_04_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_13

theorem row_00_04_03_14 : b4RowContribution (![0, 4, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 21 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 21^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_14

theorem weighted_00_04_03_14 : b4RawGapContribution ![0, 4, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 14] = b4GapPatternWeight 4 3 14 * 0 :=
      b4GapContribution_from_row 0 4 3 14 0 row_00_04_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_14

theorem row_00_04_03_15 : b4RowContribution (![0, 4, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 22 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 22^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_15

theorem weighted_00_04_03_15 : b4RawGapContribution ![0, 4, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 15] = b4GapPatternWeight 4 3 15 * 0 :=
      b4GapContribution_from_row 0 4 3 15 0 row_00_04_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_15

theorem row_00_04_03_16 : b4RowContribution (![0, 4, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 23 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 594 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 23^2 = 594
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_16

theorem weighted_00_04_03_16 : b4RawGapContribution ![0, 4, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 16] = b4GapPatternWeight 4 3 16 * 0 :=
      b4GapContribution_from_row 0 4 3 16 0 row_00_04_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_16

theorem row_00_04_03_17 : b4RowContribution (![0, 4, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 24 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 641 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 24^2 = 641
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_17

theorem weighted_00_04_03_17 : b4RawGapContribution ![0, 4, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 17] = b4GapPatternWeight 4 3 17 * 0 :=
      b4GapContribution_from_row 0 4 3 17 0 row_00_04_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_17

theorem row_00_04_03_18 : b4RowContribution (![0, 4, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 25 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 690 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 25^2 = 690
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_18

theorem weighted_00_04_03_18 : b4RawGapContribution ![0, 4, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 18] = b4GapPatternWeight 4 3 18 * 0 :=
      b4GapContribution_from_row 0 4 3 18 0 row_00_04_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_18

theorem row_00_04_03_19 : b4RowContribution (![0, 4, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 7, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 7 + 26 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 741 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 7^2 + 26^2 = 741
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_03_19

theorem weighted_00_04_03_19 : b4RawGapContribution ![0, 4, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 3, 19] = b4GapPatternWeight 4 3 19 * 0 :=
      b4GapContribution_from_row 0 4 3 19 0 row_00_04_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_03_19

def dvalues_00_04_03 : Fin 20 → ℕ := ![0, 0, 0, 0, 24, 0, 1128, 0, 816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_03

theorem dblock_00_04_03 : b4GapPatternDBlock 0 4 3 = 1968 := by
  calc
    b4GapPatternDBlock 0 4 3 = ∑ d : Fin 20, dvalues_00_04_03 d := by
      apply b4GapDBlock_of_rows 0 4 3 dvalues_00_04_03
      intro d
      fin_cases d
      · exact weighted_00_04_03_00
      · exact weighted_00_04_03_01
      · exact weighted_00_04_03_02
      · exact weighted_00_04_03_03
      · exact weighted_00_04_03_04
      · exact weighted_00_04_03_05
      · exact weighted_00_04_03_06
      · exact weighted_00_04_03_07
      · exact weighted_00_04_03_08
      · exact weighted_00_04_03_09
      · exact weighted_00_04_03_10
      · exact weighted_00_04_03_11
      · exact weighted_00_04_03_12
      · exact weighted_00_04_03_13
      · exact weighted_00_04_03_14
      · exact weighted_00_04_03_15
      · exact weighted_00_04_03_16
      · exact weighted_00_04_03_17
      · exact weighted_00_04_03_18
      · exact weighted_00_04_03_19
    _ = 1968 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_03

end Paper7MomentGapNumeric
