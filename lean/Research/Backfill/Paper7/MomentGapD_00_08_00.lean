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

theorem row_00_08_00_00 : b4RowContribution (![0, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 8 = 24
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 192 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 192
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_00

theorem weighted_00_08_00_00 : b4RawGapContribution ![0, 8, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 0] = b4GapPatternWeight 8 0 0 * 0 :=
      b4GapContribution_from_row 0 8 0 0 0 row_00_08_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_00

theorem row_00_08_00_01 : b4RowContribution (![0, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 9 = 25
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 209
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_01

theorem weighted_00_08_00_01 : b4RawGapContribution ![0, 8, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 1] = b4GapPatternWeight 8 0 1 * 0 :=
      b4GapContribution_from_row 0 8 0 1 0 row_00_08_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_01

def layers_00_08_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 53, 60, 65, 68, 69, 68, 65, 60, 53, 45]]
#print axioms Paper7MomentGapNumeric.layers_00_08_00_02

theorem cells_00_08_00_02 : QTableValid (![0, 8, 8, 10] : Fin 4 → ℕ) layers_00_08_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_08_00_02

theorem valid_00_08_00_02 :
    SparseRowValid (![0, 8, 8, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_08_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 8, 8, 10] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 8 + 8 + 10 = 26
      decide
    have hzsq : (∑ i, (((![0, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_08_00_02
#print axioms Paper7MomentGapNumeric.valid_00_08_00_02

def qvalues_00_08_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_08_00_02

theorem row_00_08_00_02 : b4RowContribution (![0, 8, 8, 10] : Fin 4 → ℕ) = 53 := by
  calc
    b4RowContribution (![0, 8, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_08_00_02) :=
      sparseRow_sound (![0, 8, 8, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_08_00_02) valid_00_08_00_02
    _ = 53 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_08_00_02 Q := by
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
        _ = 53 := by decide
#print axioms Paper7MomentGapNumeric.row_00_08_00_02

theorem weighted_00_08_00_02 : b4RawGapContribution ![0, 8, 0, 2] = 636 := by
  calc
    b4RawGapContribution ![0, 8, 0, 2] = b4GapPatternWeight 8 0 2 * 53 :=
      b4GapContribution_from_row 0 8 0 2 53 row_00_08_00_02
    _ = 636 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_02

theorem row_00_08_00_03 : b4RowContribution (![0, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 11 = 27
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_03

theorem weighted_00_08_00_03 : b4RawGapContribution ![0, 8, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 3] = b4GapPatternWeight 8 0 3 * 0 :=
      b4GapContribution_from_row 0 8 0 3 0 row_00_08_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_03

def layers_00_08_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 53, 60, 66, 71, 74, 75, 74, 71, 66, 60]]
#print axioms Paper7MomentGapNumeric.layers_00_08_00_04

theorem cells_00_08_00_04 : QTableValid (![0, 8, 8, 12] : Fin 4 → ℕ) layers_00_08_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_08_00_04

theorem valid_00_08_00_04 :
    SparseRowValid (![0, 8, 8, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_08_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 8, 8, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 8 + 8 + 12 = 28
      decide
    have hzsq : (∑ i, (((![0, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 272 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 272
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_08_00_04
#print axioms Paper7MomentGapNumeric.valid_00_08_00_04

def qvalues_00_08_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_08_00_04

theorem row_00_08_00_04 : b4RowContribution (![0, 8, 8, 12] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![0, 8, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_08_00_04) :=
      sparseRow_sound (![0, 8, 8, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_08_00_04) valid_00_08_00_04
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_08_00_04 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_00_08_00_04

theorem weighted_00_08_00_04 : b4RawGapContribution ![0, 8, 0, 4] = 540 := by
  calc
    b4RawGapContribution ![0, 8, 0, 4] = b4GapPatternWeight 8 0 4 * 45 :=
      b4GapContribution_from_row 0 8 0 4 45 row_00_08_00_04
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_04

theorem row_00_08_00_05 : b4RowContribution (![0, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 13 = 29
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_05

theorem weighted_00_08_00_05 : b4RawGapContribution ![0, 8, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 5] = b4GapPatternWeight 8 0 5 * 0 :=
      b4GapContribution_from_row 0 8 0 5 0 row_00_08_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_05

theorem row_00_08_00_06 : b4RowContribution (![0, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_06

theorem weighted_00_08_00_06 : b4RawGapContribution ![0, 8, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 6] = b4GapPatternWeight 8 0 6 * 0 :=
      b4GapContribution_from_row 0 8 0 6 0 row_00_08_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_06

theorem row_00_08_00_07 : b4RowContribution (![0, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_07

theorem weighted_00_08_00_07 : b4RawGapContribution ![0, 8, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 7] = b4GapPatternWeight 8 0 7 * 0 :=
      b4GapContribution_from_row 0 8 0 7 0 row_00_08_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_07

theorem row_00_08_00_08 : b4RowContribution (![0, 8, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 384 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 16^2 = 384
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_08

theorem weighted_00_08_00_08 : b4RawGapContribution ![0, 8, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 8] = b4GapPatternWeight 8 0 8 * 0 :=
      b4GapContribution_from_row 0 8 0 8 0 row_00_08_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_08

theorem row_00_08_00_09 : b4RowContribution (![0, 8, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 17^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_09

theorem weighted_00_08_00_09 : b4RawGapContribution ![0, 8, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 9] = b4GapPatternWeight 8 0 9 * 0 :=
      b4GapContribution_from_row 0 8 0 9 0 row_00_08_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_09

theorem row_00_08_00_10 : b4RowContribution (![0, 8, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 452 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 18^2 = 452
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_10

theorem weighted_00_08_00_10 : b4RawGapContribution ![0, 8, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 10] = b4GapPatternWeight 8 0 10 * 0 :=
      b4GapContribution_from_row 0 8 0 10 0 row_00_08_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_10

theorem row_00_08_00_11 : b4RowContribution (![0, 8, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 19^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_11

theorem weighted_00_08_00_11 : b4RawGapContribution ![0, 8, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 11] = b4GapPatternWeight 8 0 11 * 0 :=
      b4GapContribution_from_row 0 8 0 11 0 row_00_08_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_11

theorem row_00_08_00_12 : b4RowContribution (![0, 8, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 528 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 20^2 = 528
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_12

theorem weighted_00_08_00_12 : b4RawGapContribution ![0, 8, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 12] = b4GapPatternWeight 8 0 12 * 0 :=
      b4GapContribution_from_row 0 8 0 12 0 row_00_08_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_12

theorem row_00_08_00_13 : b4RowContribution (![0, 8, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 8, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 8 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 8, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 569 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 8^2 + 21^2 = 569
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_00_13

theorem weighted_00_08_00_13 : b4RawGapContribution ![0, 8, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 0, 13] = b4GapPatternWeight 8 0 13 * 0 :=
      b4GapContribution_from_row 0 8 0 13 0 row_00_08_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_00_13

def dvalues_00_08_00 : Fin 14 → ℕ := ![0, 0, 636, 0, 540, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_08_00

theorem dblock_00_08_00 : b4GapPatternDBlock 0 8 0 = 1176 := by
  calc
    b4GapPatternDBlock 0 8 0 = ∑ d : Fin 14, dvalues_00_08_00 d := by
      apply b4GapDBlock_of_rows 0 8 0 dvalues_00_08_00
      intro d
      fin_cases d
      · exact weighted_00_08_00_00
      · exact weighted_00_08_00_01
      · exact weighted_00_08_00_02
      · exact weighted_00_08_00_03
      · exact weighted_00_08_00_04
      · exact weighted_00_08_00_05
      · exact weighted_00_08_00_06
      · exact weighted_00_08_00_07
      · exact weighted_00_08_00_08
      · exact weighted_00_08_00_09
      · exact weighted_00_08_00_10
      · exact weighted_00_08_00_11
      · exact weighted_00_08_00_12
      · exact weighted_00_08_00_13
    _ = 1176 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_08_00

end Paper7MomentGapNumeric
