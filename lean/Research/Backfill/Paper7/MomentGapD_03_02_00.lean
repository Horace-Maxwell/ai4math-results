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

theorem row_03_02_00_00 : b4RowContribution (![3, 5, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 5] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 5 = 18
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 84 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 5^2 = 84
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_00

theorem weighted_03_02_00_00 : b4RawGapContribution ![3, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 3 2 0 0 0 row_03_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_00

theorem row_03_02_00_01 : b4RowContribution (![3, 5, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 6] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 6 = 19
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 95 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 6^2 = 95
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_01

theorem weighted_03_02_00_01 : b4RawGapContribution ![3, 2, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 0 :=
      b4GapContribution_from_row 3 2 0 1 0 row_03_02_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_01

theorem row_03_02_00_02 : b4RowContribution (![3, 5, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 7 = 20
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 7^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_02

theorem weighted_03_02_00_02 : b4RawGapContribution ![3, 2, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 0 :=
      b4GapContribution_from_row 3 2 0 2 0 row_03_02_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_02

theorem row_03_02_00_03 : b4RowContribution (![3, 5, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 8 = 21
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 8^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_03

theorem weighted_03_02_00_03 : b4RawGapContribution ![3, 2, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 0 :=
      b4GapContribution_from_row 3 2 0 3 0 row_03_02_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_03

theorem row_03_02_00_04 : b4RowContribution (![3, 5, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 9 = 22
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 140 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 9^2 = 140
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_04

theorem weighted_03_02_00_04 : b4RawGapContribution ![3, 2, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 0 :=
      b4GapContribution_from_row 3 2 0 4 0 row_03_02_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_04

theorem row_03_02_00_05 : b4RowContribution (![3, 5, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 10 = 23
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 159 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 10^2 = 159
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_05

theorem weighted_03_02_00_05 : b4RawGapContribution ![3, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 3 2 0 5 0 row_03_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_05

theorem row_03_02_00_06 : b4RowContribution (![3, 5, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 11 = 24
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 11^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_06

theorem weighted_03_02_00_06 : b4RawGapContribution ![3, 2, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 0 :=
      b4GapContribution_from_row 3 2 0 6 0 row_03_02_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_06

theorem row_03_02_00_07 : b4RowContribution (![3, 5, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 12 = 25
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 12^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_07

theorem weighted_03_02_00_07 : b4RawGapContribution ![3, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 3 2 0 7 0 row_03_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_07

def layers_03_02_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 20, 20, 18, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 52, 72, 92, 110, 124, 134, 140, 143, 144, 143, 140, 134, 124, 110]]
#print axioms Paper7MomentGapNumeric.layers_03_02_00_08

theorem cells_03_02_00_08 : QTableValid (![3, 5, 5, 13] : Fin 4 → ℕ) layers_03_02_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_00_08

theorem valid_03_02_00_08 :
    SparseRowValid (![3, 5, 5, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_02_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 5, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 5 + 13 = 26
      decide
    have hzsq : (∑ i, (((![3, 5, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 5^2 + 13^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_00_08
#print axioms Paper7MomentGapNumeric.valid_03_02_00_08

def qvalues_03_02_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_00_08

theorem row_03_02_00_08 : b4RowContribution (![3, 5, 5, 13] : Fin 4 → ℕ) = 124 := by
  calc
    b4RowContribution (![3, 5, 5, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_03_02_00_08) :=
      sparseRow_sound (![3, 5, 5, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_02_00_08) valid_03_02_00_08
    _ = 124 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_00_08 Q := by
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
        _ = 124 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_00_08

theorem weighted_03_02_00_08 : b4RawGapContribution ![3, 2, 0, 8] = 1488 := by
  calc
    b4RawGapContribution ![3, 2, 0, 8] = b4GapPatternWeight 2 0 8 * 124 :=
      b4GapContribution_from_row 3 2 0 8 124 row_03_02_00_08
    _ = 1488 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_08

theorem row_03_02_00_09 : b4RowContribution (![3, 5, 5, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 14 = 27
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 14^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_09

theorem weighted_03_02_00_09 : b4RawGapContribution ![3, 2, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 9] = b4GapPatternWeight 2 0 9 * 0 :=
      b4GapContribution_from_row 3 2 0 9 0 row_03_02_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_09

def layers_03_02_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 20, 20, 18, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 52, 72, 92, 110, 124, 134, 140, 143, 144, 144, 144, 143, 140, 134]]
#print axioms Paper7MomentGapNumeric.layers_03_02_00_10

theorem cells_03_02_00_10 : QTableValid (![3, 5, 5, 15] : Fin 4 → ℕ) layers_03_02_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_00_10

theorem valid_03_02_00_10 :
    SparseRowValid (![3, 5, 5, 15] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_03_02_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 5, 15] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 5 + 15 = 28
      decide
    have hzsq : (∑ i, (((![3, 5, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 5^2 + 15^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_00_10
#print axioms Paper7MomentGapNumeric.valid_03_02_00_10

def qvalues_03_02_00_10 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_00_10

theorem row_03_02_00_10 : b4RowContribution (![3, 5, 5, 15] : Fin 4 → ℕ) = 120 := by
  calc
    b4RowContribution (![3, 5, 5, 15] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_03_02_00_10) :=
      sparseRow_sound (![3, 5, 5, 15] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_03_02_00_10) valid_03_02_00_10
    _ = 120 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_00_10 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_00_10

theorem weighted_03_02_00_10 : b4RawGapContribution ![3, 2, 0, 10] = 1440 := by
  calc
    b4RawGapContribution ![3, 2, 0, 10] = b4GapPatternWeight 2 0 10 * 120 :=
      b4GapContribution_from_row 3 2 0 10 120 row_03_02_00_10
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_10

theorem row_03_02_00_11 : b4RowContribution (![3, 5, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 16 = 29
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 16^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_11

theorem weighted_03_02_00_11 : b4RawGapContribution ![3, 2, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 11] = b4GapPatternWeight 2 0 11 * 0 :=
      b4GapContribution_from_row 3 2 0 11 0 row_03_02_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_11

theorem row_03_02_00_12 : b4RowContribution (![3, 5, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 17 = 30
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 17^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_12

theorem weighted_03_02_00_12 : b4RawGapContribution ![3, 2, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 12] = b4GapPatternWeight 2 0 12 * 0 :=
      b4GapContribution_from_row 3 2 0 12 0 row_03_02_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_12

theorem row_03_02_00_13 : b4RowContribution (![3, 5, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 18 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 18^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_13

theorem weighted_03_02_00_13 : b4RawGapContribution ![3, 2, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 13] = b4GapPatternWeight 2 0 13 * 0 :=
      b4GapContribution_from_row 3 2 0 13 0 row_03_02_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_13

theorem row_03_02_00_14 : b4RowContribution (![3, 5, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 19 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 19^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_14

theorem weighted_03_02_00_14 : b4RawGapContribution ![3, 2, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 14] = b4GapPatternWeight 2 0 14 * 0 :=
      b4GapContribution_from_row 3 2 0 14 0 row_03_02_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_14

theorem row_03_02_00_15 : b4RowContribution (![3, 5, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 20 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 20^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_15

theorem weighted_03_02_00_15 : b4RawGapContribution ![3, 2, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 15] = b4GapPatternWeight 2 0 15 * 0 :=
      b4GapContribution_from_row 3 2 0 15 0 row_03_02_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_15

theorem row_03_02_00_16 : b4RowContribution (![3, 5, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 21 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 500 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 21^2 = 500
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_16

theorem weighted_03_02_00_16 : b4RawGapContribution ![3, 2, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 16] = b4GapPatternWeight 2 0 16 * 0 :=
      b4GapContribution_from_row 3 2 0 16 0 row_03_02_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_16

theorem row_03_02_00_17 : b4RowContribution (![3, 5, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 22 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 543 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 22^2 = 543
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_17

theorem weighted_03_02_00_17 : b4RawGapContribution ![3, 2, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 17] = b4GapPatternWeight 2 0 17 * 0 :=
      b4GapContribution_from_row 3 2 0 17 0 row_03_02_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_17

theorem row_03_02_00_18 : b4RowContribution (![3, 5, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 23 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 588 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 23^2 = 588
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_18

theorem weighted_03_02_00_18 : b4RawGapContribution ![3, 2, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 18] = b4GapPatternWeight 2 0 18 * 0 :=
      b4GapContribution_from_row 3 2 0 18 0 row_03_02_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_18

theorem row_03_02_00_19 : b4RowContribution (![3, 5, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 5, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 5 + 24 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 635 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 5^2 + 24^2 = 635
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_00_19

theorem weighted_03_02_00_19 : b4RawGapContribution ![3, 2, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 0, 19] = b4GapPatternWeight 2 0 19 * 0 :=
      b4GapContribution_from_row 3 2 0 19 0 row_03_02_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_00_19

def dvalues_03_02_00 : Fin 20 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 1488, 0, 1440, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_00

theorem dblock_03_02_00 : b4GapPatternDBlock 3 2 0 = 2928 := by
  calc
    b4GapPatternDBlock 3 2 0 = ∑ d : Fin 20, dvalues_03_02_00 d := by
      apply b4GapDBlock_of_rows 3 2 0 dvalues_03_02_00
      intro d
      fin_cases d
      · exact weighted_03_02_00_00
      · exact weighted_03_02_00_01
      · exact weighted_03_02_00_02
      · exact weighted_03_02_00_03
      · exact weighted_03_02_00_04
      · exact weighted_03_02_00_05
      · exact weighted_03_02_00_06
      · exact weighted_03_02_00_07
      · exact weighted_03_02_00_08
      · exact weighted_03_02_00_09
      · exact weighted_03_02_00_10
      · exact weighted_03_02_00_11
      · exact weighted_03_02_00_12
      · exact weighted_03_02_00_13
      · exact weighted_03_02_00_14
      · exact weighted_03_02_00_15
      · exact weighted_03_02_00_16
      · exact weighted_03_02_00_17
      · exact weighted_03_02_00_18
      · exact weighted_03_02_00_19
    _ = 2928 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_00

end Paper7MomentGapNumeric
