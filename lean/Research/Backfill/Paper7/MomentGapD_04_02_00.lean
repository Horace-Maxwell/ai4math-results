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

theorem row_04_02_00_00 : b4RowContribution (![4, 6, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 6] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 6 = 22
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 6^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_00

theorem weighted_04_02_00_00 : b4RawGapContribution ![4, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 4 2 0 0 0 row_04_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_00

theorem row_04_02_00_01 : b4RowContribution (![4, 6, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 7] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 7 = 23
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 137 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 7^2 = 137
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_01

theorem weighted_04_02_00_01 : b4RawGapContribution ![4, 2, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 0 :=
      b4GapContribution_from_row 4 2 0 1 0 row_04_02_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_01

theorem row_04_02_00_02 : b4RowContribution (![4, 6, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 8 = 24
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 152 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 8^2 = 152
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_02

theorem weighted_04_02_00_02 : b4RawGapContribution ![4, 2, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 0 :=
      b4GapContribution_from_row 4 2 0 2 0 row_04_02_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_02

theorem row_04_02_00_03 : b4RowContribution (![4, 6, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 9 = 25
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 9^2 = 169
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_03

theorem weighted_04_02_00_03 : b4RawGapContribution ![4, 2, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 0 :=
      b4GapContribution_from_row 4 2 0 3 0 row_04_02_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_03

theorem row_04_02_00_04 : b4RowContribution (![4, 6, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 10 = 26
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 10^2 = 188
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_04

theorem weighted_04_02_00_04 : b4RawGapContribution ![4, 2, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 0 :=
      b4GapContribution_from_row 4 2 0 4 0 row_04_02_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_04

theorem row_04_02_00_05 : b4RowContribution (![4, 6, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 11 = 27
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 11^2 = 209
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_05

theorem weighted_04_02_00_05 : b4RawGapContribution ![4, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 4 2 0 5 0 row_04_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_05

def layers_04_02_00_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 28, 29, 28, 25, 20, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 55, 80, 108, 137, 165, 190, 210, 225, 234, 237, 234, 225, 210, 190]]
#print axioms Paper7MomentGapNumeric.layers_04_02_00_06

theorem cells_04_02_00_06 : QTableValid (![4, 6, 6, 12] : Fin 4 → ℕ) layers_04_02_00_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_00_06

theorem valid_04_02_00_06 :
    SparseRowValid (![4, 6, 6, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_02_00_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 6, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 6 + 12 = 28
      decide
    have hzsq : (∑ i, (((![4, 6, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 232 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 6^2 + 12^2 = 232
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_00_06
#print axioms Paper7MomentGapNumeric.valid_04_02_00_06

def qvalues_04_02_00_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_00_06

theorem row_04_02_00_06 : b4RowContribution (![4, 6, 6, 12] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 6, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_02_00_06) :=
      sparseRow_sound (![4, 6, 6, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_02_00_06) valid_04_02_00_06
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_00_06 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_02_00_06

theorem weighted_04_02_00_06 : b4RawGapContribution ![4, 2, 0, 6] = 420 := by
  calc
    b4RawGapContribution ![4, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 35 :=
      b4GapContribution_from_row 4 2 0 6 35 row_04_02_00_06
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_06

theorem row_04_02_00_07 : b4RowContribution (![4, 6, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 13 = 29
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 13^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_07

theorem weighted_04_02_00_07 : b4RawGapContribution ![4, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 4 2 0 7 0 row_04_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_07

def layers_04_02_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 28, 29, 28, 25, 20, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 55, 80, 108, 137, 165, 190, 210, 225, 235, 241, 243, 241, 235, 225]]
#print axioms Paper7MomentGapNumeric.layers_04_02_00_08

theorem cells_04_02_00_08 : QTableValid (![4, 6, 6, 14] : Fin 4 → ℕ) layers_04_02_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_00_08

theorem valid_04_02_00_08 :
    SparseRowValid (![4, 6, 6, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_02_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 6, 14] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 6 + 14 = 30
      decide
    have hzsq : (∑ i, (((![4, 6, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 6^2 + 14^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_00_08
#print axioms Paper7MomentGapNumeric.valid_04_02_00_08

def qvalues_04_02_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_00_08

theorem row_04_02_00_08 : b4RowContribution (![4, 6, 6, 14] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![4, 6, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_04_02_00_08) :=
      sparseRow_sound (![4, 6, 6, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_02_00_08) valid_04_02_00_08
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_00_08 Q := by
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
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_04_02_00_08

theorem weighted_04_02_00_08 : b4RawGapContribution ![4, 2, 0, 8] = 660 := by
  calc
    b4RawGapContribution ![4, 2, 0, 8] = b4GapPatternWeight 2 0 8 * 55 :=
      b4GapContribution_from_row 4 2 0 8 55 row_04_02_00_08
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_08

theorem row_04_02_00_09 : b4RowContribution (![4, 6, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 15 = 31
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 15^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_09

theorem weighted_04_02_00_09 : b4RawGapContribution ![4, 2, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 9] = b4GapPatternWeight 2 0 9 * 0 :=
      b4GapContribution_from_row 4 2 0 9 0 row_04_02_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_09

theorem row_04_02_00_10 : b4RowContribution (![4, 6, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 16 = 32
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 344 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 16^2 = 344
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_10

theorem weighted_04_02_00_10 : b4RawGapContribution ![4, 2, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 10] = b4GapPatternWeight 2 0 10 * 0 :=
      b4GapContribution_from_row 4 2 0 10 0 row_04_02_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_10

theorem row_04_02_00_11 : b4RowContribution (![4, 6, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 17 = 33
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 17^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_11

theorem weighted_04_02_00_11 : b4RawGapContribution ![4, 2, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 11] = b4GapPatternWeight 2 0 11 * 0 :=
      b4GapContribution_from_row 4 2 0 11 0 row_04_02_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_11

theorem row_04_02_00_12 : b4RowContribution (![4, 6, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 18 = 34
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 412 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 18^2 = 412
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_12

theorem weighted_04_02_00_12 : b4RawGapContribution ![4, 2, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 12] = b4GapPatternWeight 2 0 12 * 0 :=
      b4GapContribution_from_row 4 2 0 12 0 row_04_02_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_12

theorem row_04_02_00_13 : b4RowContribution (![4, 6, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 19 = 35
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 19^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_13

theorem weighted_04_02_00_13 : b4RawGapContribution ![4, 2, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 13] = b4GapPatternWeight 2 0 13 * 0 :=
      b4GapContribution_from_row 4 2 0 13 0 row_04_02_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_13

theorem row_04_02_00_14 : b4RowContribution (![4, 6, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 20 = 36
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 488 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 20^2 = 488
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_14

theorem weighted_04_02_00_14 : b4RawGapContribution ![4, 2, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 14] = b4GapPatternWeight 2 0 14 * 0 :=
      b4GapContribution_from_row 4 2 0 14 0 row_04_02_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_14

theorem row_04_02_00_15 : b4RowContribution (![4, 6, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 6, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 6 + 21 = 37
    decide
  have hzsq : (∑ i, (((![4, 6, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 6^2 + 21^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_00_15

theorem weighted_04_02_00_15 : b4RawGapContribution ![4, 2, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 0, 15] = b4GapPatternWeight 2 0 15 * 0 :=
      b4GapContribution_from_row 4 2 0 15 0 row_04_02_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_00_15

def dvalues_04_02_00 : Fin 16 → ℕ := ![0, 0, 0, 0, 0, 0, 420, 0, 660, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_02_00

theorem dblock_04_02_00 : b4GapPatternDBlock 4 2 0 = 1080 := by
  calc
    b4GapPatternDBlock 4 2 0 = ∑ d : Fin 16, dvalues_04_02_00 d := by
      apply b4GapDBlock_of_rows 4 2 0 dvalues_04_02_00
      intro d
      fin_cases d
      · exact weighted_04_02_00_00
      · exact weighted_04_02_00_01
      · exact weighted_04_02_00_02
      · exact weighted_04_02_00_03
      · exact weighted_04_02_00_04
      · exact weighted_04_02_00_05
      · exact weighted_04_02_00_06
      · exact weighted_04_02_00_07
      · exact weighted_04_02_00_08
      · exact weighted_04_02_00_09
      · exact weighted_04_02_00_10
      · exact weighted_04_02_00_11
      · exact weighted_04_02_00_12
      · exact weighted_04_02_00_13
      · exact weighted_04_02_00_14
      · exact weighted_04_02_00_15
    _ = 1080 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_02_00

end Paper7MomentGapNumeric
