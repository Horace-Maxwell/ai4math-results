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

theorem row_03_00_05_00 : b4RowContribution (![3, 3, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 8 = 22
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 8^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_00

theorem weighted_03_00_05_00 : b4RawGapContribution ![3, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 3 0 5 0 0 row_03_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_00

theorem row_03_00_05_01 : b4RowContribution (![3, 3, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 9 = 23
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 9^2 = 163
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_01

theorem weighted_03_00_05_01 : b4RawGapContribution ![3, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 3 0 5 1 0 row_03_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_01

theorem row_03_00_05_02 : b4RowContribution (![3, 3, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 10 = 24
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 10^2 = 182
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_02

theorem weighted_03_00_05_02 : b4RawGapContribution ![3, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 3 0 5 2 0 row_03_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_02

theorem row_03_00_05_03 : b4RowContribution (![3, 3, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 11 = 25
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 11^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_03

theorem weighted_03_00_05_03 : b4RawGapContribution ![3, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 3 0 5 3 0 row_03_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_03

def layers_03_00_05_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 96, 111, 124, 134, 140, 142, 140, 134, 124, 111, 96]]
#print axioms Paper7MomentGapNumeric.layers_03_00_05_04

theorem cells_03_00_05_04 : QTableValid (![3, 3, 8, 12] : Fin 4 → ℕ) layers_03_00_05_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_05_04

theorem valid_03_00_05_04 :
    SparseRowValid (![3, 3, 8, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_03_00_05_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 8, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 8 + 12 = 26
      decide
    have hzsq : (∑ i, (((![3, 3, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 8^2 + 12^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_05_04
#print axioms Paper7MomentGapNumeric.valid_03_00_05_04

def qvalues_03_00_05_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_05_04

theorem row_03_00_05_04 : b4RowContribution (![3, 3, 8, 12] : Fin 4 → ℕ) = 124 := by
  calc
    b4RowContribution (![3, 3, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_03_00_05_04) :=
      sparseRow_sound (![3, 3, 8, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_03_00_05_04) valid_03_00_05_04
    _ = 124 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_05_04 Q := by
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
        _ = 124 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_05_04

theorem weighted_03_00_05_04 : b4RawGapContribution ![3, 0, 5, 4] = 1488 := by
  calc
    b4RawGapContribution ![3, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 124 :=
      b4GapContribution_from_row 3 0 5 4 124 row_03_00_05_04
    _ = 1488 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_04

theorem row_03_00_05_05 : b4RowContribution (![3, 3, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 13 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 13^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_05

theorem weighted_03_00_05_05 : b4RawGapContribution ![3, 0, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 0 :=
      b4GapContribution_from_row 3 0 5 5 0 row_03_00_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_05

def layers_03_00_05_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 96, 111, 124, 134, 140, 143, 144, 143, 140, 134, 124]]
#print axioms Paper7MomentGapNumeric.layers_03_00_05_06

theorem cells_03_00_05_06 : QTableValid (![3, 3, 8, 14] : Fin 4 → ℕ) layers_03_00_05_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_05_06

theorem valid_03_00_05_06 :
    SparseRowValid (![3, 3, 8, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_05_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 8, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 8 + 14 = 28
      decide
    have hzsq : (∑ i, (((![3, 3, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 8^2 + 14^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_05_06
#print axioms Paper7MomentGapNumeric.valid_03_00_05_06

def qvalues_03_00_05_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_05_06

theorem row_03_00_05_06 : b4RowContribution (![3, 3, 8, 14] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![3, 3, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_00_05_06) :=
      sparseRow_sound (![3, 3, 8, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_05_06) valid_03_00_05_06
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_05_06 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_05_06

theorem weighted_03_00_05_06 : b4RawGapContribution ![3, 0, 5, 6] = 576 := by
  calc
    b4RawGapContribution ![3, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 48 :=
      b4GapContribution_from_row 3 0 5 6 48 row_03_00_05_06
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_06

theorem row_03_00_05_07 : b4RowContribution (![3, 3, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 15 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 15^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_07

theorem weighted_03_00_05_07 : b4RawGapContribution ![3, 0, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 0 :=
      b4GapContribution_from_row 3 0 5 7 0 row_03_00_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_07

theorem row_03_00_05_08 : b4RowContribution (![3, 3, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 16 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 16^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_08

theorem weighted_03_00_05_08 : b4RawGapContribution ![3, 0, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 8] = b4GapPatternWeight 0 5 8 * 0 :=
      b4GapContribution_from_row 3 0 5 8 0 row_03_00_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_08

theorem row_03_00_05_09 : b4RowContribution (![3, 3, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 17 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 17^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_09

theorem weighted_03_00_05_09 : b4RawGapContribution ![3, 0, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 9] = b4GapPatternWeight 0 5 9 * 0 :=
      b4GapContribution_from_row 3 0 5 9 0 row_03_00_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_09

theorem row_03_00_05_10 : b4RowContribution (![3, 3, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 18 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 18^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_10

theorem weighted_03_00_05_10 : b4RawGapContribution ![3, 0, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 10] = b4GapPatternWeight 0 5 10 * 0 :=
      b4GapContribution_from_row 3 0 5 10 0 row_03_00_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_10

theorem row_03_00_05_11 : b4RowContribution (![3, 3, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 19 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 19^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_11

theorem weighted_03_00_05_11 : b4RawGapContribution ![3, 0, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 11] = b4GapPatternWeight 0 5 11 * 0 :=
      b4GapContribution_from_row 3 0 5 11 0 row_03_00_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_11

theorem row_03_00_05_12 : b4RowContribution (![3, 3, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 20 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 20^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_12

theorem weighted_03_00_05_12 : b4RawGapContribution ![3, 0, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 12] = b4GapPatternWeight 0 5 12 * 0 :=
      b4GapContribution_from_row 3 0 5 12 0 row_03_00_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_12

theorem row_03_00_05_13 : b4RowContribution (![3, 3, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 21 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 523 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 21^2 = 523
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_13

theorem weighted_03_00_05_13 : b4RawGapContribution ![3, 0, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 13] = b4GapPatternWeight 0 5 13 * 0 :=
      b4GapContribution_from_row 3 0 5 13 0 row_03_00_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_13

theorem row_03_00_05_14 : b4RowContribution (![3, 3, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 22 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 22^2 = 566
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_14

theorem weighted_03_00_05_14 : b4RawGapContribution ![3, 0, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 14] = b4GapPatternWeight 0 5 14 * 0 :=
      b4GapContribution_from_row 3 0 5 14 0 row_03_00_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_14

theorem row_03_00_05_15 : b4RowContribution (![3, 3, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 8, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 8 + 23 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 611 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 8^2 + 23^2 = 611
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_05_15

theorem weighted_03_00_05_15 : b4RawGapContribution ![3, 0, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 5, 15] = b4GapPatternWeight 0 5 15 * 0 :=
      b4GapContribution_from_row 3 0 5 15 0 row_03_00_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_05_15

def dvalues_03_00_05 : Fin 16 → ℕ := ![0, 0, 0, 0, 1488, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_05

theorem dblock_03_00_05 : b4GapPatternDBlock 3 0 5 = 2064 := by
  calc
    b4GapPatternDBlock 3 0 5 = ∑ d : Fin 16, dvalues_03_00_05 d := by
      apply b4GapDBlock_of_rows 3 0 5 dvalues_03_00_05
      intro d
      fin_cases d
      · exact weighted_03_00_05_00
      · exact weighted_03_00_05_01
      · exact weighted_03_00_05_02
      · exact weighted_03_00_05_03
      · exact weighted_03_00_05_04
      · exact weighted_03_00_05_05
      · exact weighted_03_00_05_06
      · exact weighted_03_00_05_07
      · exact weighted_03_00_05_08
      · exact weighted_03_00_05_09
      · exact weighted_03_00_05_10
      · exact weighted_03_00_05_11
      · exact weighted_03_00_05_12
      · exact weighted_03_00_05_13
      · exact weighted_03_00_05_14
      · exact weighted_03_00_05_15
    _ = 2064 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_05

end Paper7MomentGapNumeric
