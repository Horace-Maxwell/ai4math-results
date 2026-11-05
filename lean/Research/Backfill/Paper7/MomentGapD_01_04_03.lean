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

theorem row_01_04_03_00 : b4RowContribution (![1, 5, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 8 = 22
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 154 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 8^2 = 154
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_00

theorem weighted_01_04_03_00 : b4RawGapContribution ![1, 4, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 0] = b4GapPatternWeight 4 3 0 * 0 :=
      b4GapContribution_from_row 1 4 3 0 0 row_01_04_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_00

theorem row_01_04_03_01 : b4RowContribution (![1, 5, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 9 = 23
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 9^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_01

theorem weighted_01_04_03_01 : b4RawGapContribution ![1, 4, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 1] = b4GapPatternWeight 4 3 1 * 0 :=
      b4GapContribution_from_row 1 4 3 1 0 row_01_04_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_01

theorem row_01_04_03_02 : b4RowContribution (![1, 5, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 10 = 24
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 10^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_02

theorem weighted_01_04_03_02 : b4RawGapContribution ![1, 4, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 2] = b4GapPatternWeight 4 3 2 * 0 :=
      b4GapContribution_from_row 1 4 3 2 0 row_01_04_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_02

theorem row_01_04_03_03 : b4RowContribution (![1, 5, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 11 = 25
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 11^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_03

theorem weighted_01_04_03_03 : b4RawGapContribution ![1, 4, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 3] = b4GapPatternWeight 4 3 3 * 0 :=
      b4GapContribution_from_row 1 4 3 3 0 row_01_04_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_03

def layers_01_04_03_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 83, 92, 99, 104, 106, 104, 99, 92, 83, 72]]
#print axioms Paper7MomentGapNumeric.layers_01_04_03_04

theorem cells_01_04_03_04 : QTableValid (![1, 5, 8, 12] : Fin 4 → ℕ) layers_01_04_03_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_03_04

theorem valid_01_04_03_04 :
    SparseRowValid (![1, 5, 8, 12] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_04_03_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 8, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 8 + 12 = 26
      decide
    have hzsq : (∑ i, (((![1, 5, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 8^2 + 12^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_03_04
#print axioms Paper7MomentGapNumeric.valid_01_04_03_04

def qvalues_01_04_03_04 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_03_04

theorem row_01_04_03_04 : b4RowContribution (![1, 5, 8, 12] : Fin 4 → ℕ) = 49 := by
  calc
    b4RowContribution (![1, 5, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_04_03_04) :=
      sparseRow_sound (![1, 5, 8, 12] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_04_03_04) valid_01_04_03_04
    _ = 49 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_03_04 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 49 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_03_04

theorem weighted_01_04_03_04 : b4RawGapContribution ![1, 4, 3, 4] = 1176 := by
  calc
    b4RawGapContribution ![1, 4, 3, 4] = b4GapPatternWeight 4 3 4 * 49 :=
      b4GapContribution_from_row 1 4 3 4 49 row_01_04_03_04
    _ = 1176 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_04

theorem row_01_04_03_05 : b4RowContribution (![1, 5, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 13 = 27
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 13^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_05

theorem weighted_01_04_03_05 : b4RawGapContribution ![1, 4, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 5] = b4GapPatternWeight 4 3 5 * 0 :=
      b4GapContribution_from_row 1 4 3 5 0 row_01_04_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_05

def layers_01_04_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 83, 92, 99, 104, 107, 108, 107, 104, 99, 92]]
#print axioms Paper7MomentGapNumeric.layers_01_04_03_06

theorem cells_01_04_03_06 : QTableValid (![1, 5, 8, 14] : Fin 4 → ℕ) layers_01_04_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_03_06

theorem valid_01_04_03_06 :
    SparseRowValid (![1, 5, 8, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_04_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 8, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 8 + 14 = 28
      decide
    have hzsq : (∑ i, (((![1, 5, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 8^2 + 14^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_03_06
#print axioms Paper7MomentGapNumeric.valid_01_04_03_06

def qvalues_01_04_03_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_03_06

theorem row_01_04_03_06 : b4RowContribution (![1, 5, 8, 14] : Fin 4 → ℕ) = 60 := by
  calc
    b4RowContribution (![1, 5, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_04_03_06) :=
      sparseRow_sound (![1, 5, 8, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_04_03_06) valid_01_04_03_06
    _ = 60 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_03_06 Q := by
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
        _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_03_06

theorem weighted_01_04_03_06 : b4RawGapContribution ![1, 4, 3, 6] = 1440 := by
  calc
    b4RawGapContribution ![1, 4, 3, 6] = b4GapPatternWeight 4 3 6 * 60 :=
      b4GapContribution_from_row 1 4 3 6 60 row_01_04_03_06
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_06

theorem row_01_04_03_07 : b4RowContribution (![1, 5, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 15^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_07

theorem weighted_01_04_03_07 : b4RawGapContribution ![1, 4, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 7] = b4GapPatternWeight 4 3 7 * 0 :=
      b4GapContribution_from_row 1 4 3 7 0 row_01_04_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_07

theorem row_01_04_03_08 : b4RowContribution (![1, 5, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 16^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_08

theorem weighted_01_04_03_08 : b4RawGapContribution ![1, 4, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 8] = b4GapPatternWeight 4 3 8 * 0 :=
      b4GapContribution_from_row 1 4 3 8 0 row_01_04_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_08

theorem row_01_04_03_09 : b4RowContribution (![1, 5, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 17^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_09

theorem weighted_01_04_03_09 : b4RawGapContribution ![1, 4, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 9] = b4GapPatternWeight 4 3 9 * 0 :=
      b4GapContribution_from_row 1 4 3 9 0 row_01_04_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_09

theorem row_01_04_03_10 : b4RowContribution (![1, 5, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 18^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_10

theorem weighted_01_04_03_10 : b4RawGapContribution ![1, 4, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 10] = b4GapPatternWeight 4 3 10 * 0 :=
      b4GapContribution_from_row 1 4 3 10 0 row_01_04_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_10

theorem row_01_04_03_11 : b4RowContribution (![1, 5, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 19^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_11

theorem weighted_01_04_03_11 : b4RawGapContribution ![1, 4, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 11] = b4GapPatternWeight 4 3 11 * 0 :=
      b4GapContribution_from_row 1 4 3 11 0 row_01_04_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_11

theorem row_01_04_03_12 : b4RowContribution (![1, 5, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 20^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_12

theorem weighted_01_04_03_12 : b4RawGapContribution ![1, 4, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 12] = b4GapPatternWeight 4 3 12 * 0 :=
      b4GapContribution_from_row 1 4 3 12 0 row_01_04_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_12

theorem row_01_04_03_13 : b4RowContribution (![1, 5, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 21 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 21^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_13

theorem weighted_01_04_03_13 : b4RawGapContribution ![1, 4, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 13] = b4GapPatternWeight 4 3 13 * 0 :=
      b4GapContribution_from_row 1 4 3 13 0 row_01_04_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_13

theorem row_01_04_03_14 : b4RowContribution (![1, 5, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 574 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 22^2 = 574
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_14

theorem weighted_01_04_03_14 : b4RawGapContribution ![1, 4, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 14] = b4GapPatternWeight 4 3 14 * 0 :=
      b4GapContribution_from_row 1 4 3 14 0 row_01_04_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_14

theorem row_01_04_03_15 : b4RowContribution (![1, 5, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 8, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 8 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 619 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 8^2 + 23^2 = 619
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_03_15

theorem weighted_01_04_03_15 : b4RawGapContribution ![1, 4, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 3, 15] = b4GapPatternWeight 4 3 15 * 0 :=
      b4GapContribution_from_row 1 4 3 15 0 row_01_04_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_03_15

def dvalues_01_04_03 : Fin 16 → ℕ := ![0, 0, 0, 0, 1176, 0, 1440, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_03

theorem dblock_01_04_03 : b4GapPatternDBlock 1 4 3 = 2616 := by
  calc
    b4GapPatternDBlock 1 4 3 = ∑ d : Fin 16, dvalues_01_04_03 d := by
      apply b4GapDBlock_of_rows 1 4 3 dvalues_01_04_03
      intro d
      fin_cases d
      · exact weighted_01_04_03_00
      · exact weighted_01_04_03_01
      · exact weighted_01_04_03_02
      · exact weighted_01_04_03_03
      · exact weighted_01_04_03_04
      · exact weighted_01_04_03_05
      · exact weighted_01_04_03_06
      · exact weighted_01_04_03_07
      · exact weighted_01_04_03_08
      · exact weighted_01_04_03_09
      · exact weighted_01_04_03_10
      · exact weighted_01_04_03_11
      · exact weighted_01_04_03_12
      · exact weighted_01_04_03_13
      · exact weighted_01_04_03_14
      · exact weighted_01_04_03_15
    _ = 2616 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_03

end Paper7MomentGapNumeric
