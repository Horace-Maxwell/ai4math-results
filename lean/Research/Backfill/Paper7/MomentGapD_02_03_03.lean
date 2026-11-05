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

theorem row_02_03_03_00 : b4RowContribution (![2, 5, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 8 = 23
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 157 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 8^2 = 157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_00

theorem weighted_02_03_03_00 : b4RawGapContribution ![2, 3, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 0] = b4GapPatternWeight 3 3 0 * 0 :=
      b4GapContribution_from_row 2 3 3 0 0 row_02_03_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_00

theorem row_02_03_03_01 : b4RowContribution (![2, 5, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 9 = 24
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 9^2 = 174
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_01

theorem weighted_02_03_03_01 : b4RawGapContribution ![2, 3, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 1] = b4GapPatternWeight 3 3 1 * 0 :=
      b4GapContribution_from_row 2 3 3 1 0 row_02_03_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_01

theorem row_02_03_03_02 : b4RowContribution (![2, 5, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 10 = 25
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 10^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_02

theorem weighted_02_03_03_02 : b4RawGapContribution ![2, 3, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 2] = b4GapPatternWeight 3 3 2 * 0 :=
      b4GapContribution_from_row 2 3 3 2 0 row_02_03_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_02

theorem row_02_03_03_03 : b4RowContribution (![2, 5, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 11 = 26
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 11^2 = 214
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_03

theorem weighted_02_03_03_03 : b4RawGapContribution ![2, 3, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 3] = b4GapPatternWeight 3 3 3 * 0 :=
      b4GapContribution_from_row 2 3 3 3 0 row_02_03_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_03

def layers_02_03_03_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 17, 15, 12, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 116, 131, 143, 152, 157, 157, 152, 143, 131, 116]]
#print axioms Paper7MomentGapNumeric.layers_02_03_03_04

theorem cells_02_03_03_04 : QTableValid (![2, 5, 8, 12] : Fin 4 → ℕ) layers_02_03_03_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_03_04

theorem valid_02_03_03_04 :
    SparseRowValid (![2, 5, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_03_03_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 8, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 8 + 12 = 27
      decide
    have hzsq : (∑ i, (((![2, 5, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 8^2 + 12^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_03_04
#print axioms Paper7MomentGapNumeric.valid_02_03_03_04

def qvalues_02_03_03_04 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_03_04

theorem row_02_03_03_04 : b4RowContribution (![2, 5, 8, 12] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![2, 5, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_03_03_04) :=
      sparseRow_sound (![2, 5, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_03_03_04) valid_02_03_03_04
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_03_04 Q := by
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
        _ = 19 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_03_04

theorem weighted_02_03_03_04 : b4RawGapContribution ![2, 3, 3, 4] = 456 := by
  calc
    b4RawGapContribution ![2, 3, 3, 4] = b4GapPatternWeight 3 3 4 * 19 :=
      b4GapContribution_from_row 2 3 3 4 19 row_02_03_03_04
    _ = 456 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_04

theorem row_02_03_03_05 : b4RowContribution (![2, 5, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 13 = 28
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 13^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_05

theorem weighted_02_03_03_05 : b4RawGapContribution ![2, 3, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 5] = b4GapPatternWeight 3 3 5 * 0 :=
      b4GapContribution_from_row 2 3 3 5 0 row_02_03_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_05

theorem row_02_03_03_06 : b4RowContribution (![2, 5, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 14 = 29
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 14^2 = 289
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_06

theorem weighted_02_03_03_06 : b4RawGapContribution ![2, 3, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 6] = b4GapPatternWeight 3 3 6 * 0 :=
      b4GapContribution_from_row 2 3 3 6 0 row_02_03_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_06

theorem row_02_03_03_07 : b4RowContribution (![2, 5, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 15 = 30
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 15^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_07

theorem weighted_02_03_03_07 : b4RawGapContribution ![2, 3, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 7] = b4GapPatternWeight 3 3 7 * 0 :=
      b4GapContribution_from_row 2 3 3 7 0 row_02_03_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_07

theorem row_02_03_03_08 : b4RowContribution (![2, 5, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 16 = 31
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 16^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_08

theorem weighted_02_03_03_08 : b4RawGapContribution ![2, 3, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 8] = b4GapPatternWeight 3 3 8 * 0 :=
      b4GapContribution_from_row 2 3 3 8 0 row_02_03_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_08

theorem row_02_03_03_09 : b4RowContribution (![2, 5, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 17 = 32
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 17^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_09

theorem weighted_02_03_03_09 : b4RawGapContribution ![2, 3, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 9] = b4GapPatternWeight 3 3 9 * 0 :=
      b4GapContribution_from_row 2 3 3 9 0 row_02_03_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_09

theorem row_02_03_03_10 : b4RowContribution (![2, 5, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 18 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 18^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_10

theorem weighted_02_03_03_10 : b4RawGapContribution ![2, 3, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 10] = b4GapPatternWeight 3 3 10 * 0 :=
      b4GapContribution_from_row 2 3 3 10 0 row_02_03_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_10

theorem row_02_03_03_11 : b4RowContribution (![2, 5, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 19 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 19^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_11

theorem weighted_02_03_03_11 : b4RawGapContribution ![2, 3, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 11] = b4GapPatternWeight 3 3 11 * 0 :=
      b4GapContribution_from_row 2 3 3 11 0 row_02_03_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_11

theorem row_02_03_03_12 : b4RowContribution (![2, 5, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 20 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 20^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_12

theorem weighted_02_03_03_12 : b4RawGapContribution ![2, 3, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 12] = b4GapPatternWeight 3 3 12 * 0 :=
      b4GapContribution_from_row 2 3 3 12 0 row_02_03_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_12

theorem row_02_03_03_13 : b4RowContribution (![2, 5, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 21 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 21^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_13

theorem weighted_02_03_03_13 : b4RawGapContribution ![2, 3, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 13] = b4GapPatternWeight 3 3 13 * 0 :=
      b4GapContribution_from_row 2 3 3 13 0 row_02_03_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_13

theorem row_02_03_03_14 : b4RowContribution (![2, 5, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 8, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 8 + 22 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 577 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 8^2 + 22^2 = 577
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_03_14

theorem weighted_02_03_03_14 : b4RawGapContribution ![2, 3, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 3, 14] = b4GapPatternWeight 3 3 14 * 0 :=
      b4GapContribution_from_row 2 3 3 14 0 row_02_03_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_03_14

def dvalues_02_03_03 : Fin 15 → ℕ := ![0, 0, 0, 0, 456, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_03

theorem dblock_02_03_03 : b4GapPatternDBlock 2 3 3 = 456 := by
  calc
    b4GapPatternDBlock 2 3 3 = ∑ d : Fin 15, dvalues_02_03_03 d := by
      apply b4GapDBlock_of_rows 2 3 3 dvalues_02_03_03
      intro d
      fin_cases d
      · exact weighted_02_03_03_00
      · exact weighted_02_03_03_01
      · exact weighted_02_03_03_02
      · exact weighted_02_03_03_03
      · exact weighted_02_03_03_04
      · exact weighted_02_03_03_05
      · exact weighted_02_03_03_06
      · exact weighted_02_03_03_07
      · exact weighted_02_03_03_08
      · exact weighted_02_03_03_09
      · exact weighted_02_03_03_10
      · exact weighted_02_03_03_11
      · exact weighted_02_03_03_12
      · exact weighted_02_03_03_13
      · exact weighted_02_03_03_14
    _ = 456 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_03

end Paper7MomentGapNumeric
