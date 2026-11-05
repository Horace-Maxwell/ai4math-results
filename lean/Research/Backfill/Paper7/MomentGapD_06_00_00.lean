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

theorem row_06_00_00_00 : b4RowContribution (![6, 6, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 6] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 6 = 24
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 144 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 6^2 = 144
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_00

theorem weighted_06_00_00_00 : b4RawGapContribution ![6, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 6 0 0 0 0 row_06_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_00

theorem row_06_00_00_01 : b4RowContribution (![6, 6, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 7] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 7 = 25
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 157 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 7^2 = 157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_01

theorem weighted_06_00_00_01 : b4RawGapContribution ![6, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 6 0 0 1 0 row_06_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_01

theorem row_06_00_00_02 : b4RowContribution (![6, 6, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 8 = 26
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 8^2 = 172
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_02

theorem weighted_06_00_00_02 : b4RawGapContribution ![6, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 6 0 0 2 0 row_06_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_02

theorem row_06_00_00_03 : b4RowContribution (![6, 6, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 9 = 27
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 9^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_03

theorem weighted_06_00_00_03 : b4RawGapContribution ![6, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 6 0 0 3 0 row_06_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_03

theorem row_06_00_00_04 : b4RowContribution (![6, 6, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 10 = 28
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 208 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 10^2 = 208
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_04

theorem weighted_06_00_00_04 : b4RawGapContribution ![6, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 6 0 0 4 0 row_06_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_04

def layers_06_00_00_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 33, 36, 37, 36, 33, 28, 21, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 56, 84, 117, 153, 190, 226, 259, 286, 304, 313, 313, 304, 286, 259]]
#print axioms Paper7MomentGapNumeric.layers_06_00_00_05

theorem cells_06_00_00_05 : QTableValid (![6, 6, 6, 11] : Fin 4 → ℕ) layers_06_00_00_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_00_00_05

theorem valid_06_00_00_05 :
    SparseRowValid (![6, 6, 6, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_06_00_00_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 6, 6, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 6 + 6 + 6 + 11 = 29
      decide
    have hzsq : (∑ i, (((![6, 6, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 6^2 + 6^2 + 11^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_00_00_05
#print axioms Paper7MomentGapNumeric.valid_06_00_00_05

def qvalues_06_00_00_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_00_00_05

theorem row_06_00_00_05 : b4RowContribution (![6, 6, 6, 11] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![6, 6, 6, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_06_00_00_05) :=
      sparseRow_sound (![6, 6, 6, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_06_00_00_05) valid_06_00_00_05
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_00_00_05 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_06_00_00_05

theorem weighted_06_00_00_05 : b4RawGapContribution ![6, 0, 0, 5] = 140 := by
  calc
    b4RawGapContribution ![6, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 35 :=
      b4GapContribution_from_row 6 0 0 5 35 row_06_00_00_05
    _ = 140 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_05

theorem row_06_00_00_06 : b4RowContribution (![6, 6, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 12 = 30
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 12^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_06

theorem weighted_06_00_00_06 : b4RawGapContribution ![6, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 6 0 0 6 0 row_06_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_06

def layers_06_00_00_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 33, 36, 37, 36, 33, 28, 21, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 56, 84, 117, 153, 190, 226, 259, 287, 308, 322, 329, 329, 322, 308]]
#print axioms Paper7MomentGapNumeric.layers_06_00_00_07

theorem cells_06_00_00_07 : QTableValid (![6, 6, 6, 13] : Fin 4 → ℕ) layers_06_00_00_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_00_00_07

theorem valid_06_00_00_07 :
    SparseRowValid (![6, 6, 6, 13] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_06_00_00_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 6, 6, 13] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 6 + 6 + 6 + 13 = 31
      decide
    have hzsq : (∑ i, (((![6, 6, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 6^2 + 6^2 + 13^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_00_00_07
#print axioms Paper7MomentGapNumeric.valid_06_00_00_07

def qvalues_06_00_00_07 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_00_00_07

theorem row_06_00_00_07 : b4RowContribution (![6, 6, 6, 13] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![6, 6, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_06_00_00_07) :=
      sparseRow_sound (![6, 6, 6, 13] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_06_00_00_07) valid_06_00_00_07
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_00_00_07 Q := by
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
#print axioms Paper7MomentGapNumeric.row_06_00_00_07

theorem weighted_06_00_00_07 : b4RawGapContribution ![6, 0, 0, 7] = 16 := by
  calc
    b4RawGapContribution ![6, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 4 :=
      b4GapContribution_from_row 6 0 0 7 4 row_06_00_00_07
    _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_07

theorem row_06_00_00_08 : b4RowContribution (![6, 6, 6, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 14 = 32
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 304 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 14^2 = 304
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_08

theorem weighted_06_00_00_08 : b4RawGapContribution ![6, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 6 0 0 8 0 row_06_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_08

theorem row_06_00_00_09 : b4RowContribution (![6, 6, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 15 = 33
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 15^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_09

theorem weighted_06_00_00_09 : b4RawGapContribution ![6, 0, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 0 :=
      b4GapContribution_from_row 6 0 0 9 0 row_06_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_09

theorem row_06_00_00_10 : b4RowContribution (![6, 6, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 16 = 34
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 16^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_10

theorem weighted_06_00_00_10 : b4RawGapContribution ![6, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 6 0 0 10 0 row_06_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_10

theorem row_06_00_00_11 : b4RowContribution (![6, 6, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 17 = 35
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 17^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_11

theorem weighted_06_00_00_11 : b4RawGapContribution ![6, 0, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 0 :=
      b4GapContribution_from_row 6 0 0 11 0 row_06_00_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_11

theorem row_06_00_00_12 : b4RowContribution (![6, 6, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 18 = 36
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 432 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 18^2 = 432
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_12

theorem weighted_06_00_00_12 : b4RawGapContribution ![6, 0, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 0 :=
      b4GapContribution_from_row 6 0 0 12 0 row_06_00_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_12

theorem row_06_00_00_13 : b4RowContribution (![6, 6, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 6, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 6 + 19 = 37
    decide
  have hzsq : (∑ i, (((![6, 6, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 6^2 + 19^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_00_13

theorem weighted_06_00_00_13 : b4RawGapContribution ![6, 0, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 0 :=
      b4GapContribution_from_row 6 0 0 13 0 row_06_00_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_00_13

def dvalues_06_00_00 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 140, 0, 16, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_00_00

theorem dblock_06_00_00 : b4GapPatternDBlock 6 0 0 = 156 := by
  calc
    b4GapPatternDBlock 6 0 0 = ∑ d : Fin 14, dvalues_06_00_00 d := by
      apply b4GapDBlock_of_rows 6 0 0 dvalues_06_00_00
      intro d
      fin_cases d
      · exact weighted_06_00_00_00
      · exact weighted_06_00_00_01
      · exact weighted_06_00_00_02
      · exact weighted_06_00_00_03
      · exact weighted_06_00_00_04
      · exact weighted_06_00_00_05
      · exact weighted_06_00_00_06
      · exact weighted_06_00_00_07
      · exact weighted_06_00_00_08
      · exact weighted_06_00_00_09
      · exact weighted_06_00_00_10
      · exact weighted_06_00_00_11
      · exact weighted_06_00_00_12
      · exact weighted_06_00_00_13
    _ = 156 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_00_00

end Paper7MomentGapNumeric
