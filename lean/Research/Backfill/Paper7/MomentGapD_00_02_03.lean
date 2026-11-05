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

theorem row_00_02_03_00 : b4RowContribution (![0, 2, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 5] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 5 = 12
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 54 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 5^2 = 54
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_00

theorem weighted_00_02_03_00 : b4RawGapContribution ![0, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 0 2 3 0 0 row_00_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_00

theorem row_00_02_03_01 : b4RowContribution (![0, 2, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 6 = 13
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 65 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 6^2 = 65
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_01

theorem weighted_00_02_03_01 : b4RawGapContribution ![0, 2, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 0 :=
      b4GapContribution_from_row 0 2 3 1 0 row_00_02_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_01

theorem row_00_02_03_02 : b4RowContribution (![0, 2, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 7 = 14
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 78 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 7^2 = 78
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_02

theorem weighted_00_02_03_02 : b4RawGapContribution ![0, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 0 2 3 2 0 row_00_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_02

theorem row_00_02_03_03 : b4RowContribution (![0, 2, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 8 = 15
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 93 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 8^2 = 93
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_03

theorem weighted_00_02_03_03 : b4RawGapContribution ![0, 2, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 0 :=
      b4GapContribution_from_row 0 2 3 3 0 row_00_02_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_03

theorem row_00_02_03_04 : b4RowContribution (![0, 2, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 9 = 16
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 110 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 9^2 = 110
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_04

theorem weighted_00_02_03_04 : b4RawGapContribution ![0, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 0 2 3 4 0 row_00_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_04

theorem row_00_02_03_05 : b4RowContribution (![0, 2, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 10 = 17
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 10^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_05

theorem weighted_00_02_03_05 : b4RawGapContribution ![0, 2, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 0 :=
      b4GapContribution_from_row 0 2 3 5 0 row_00_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_05

theorem row_00_02_03_06 : b4RowContribution (![0, 2, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 11 = 18
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 11^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_06

theorem weighted_00_02_03_06 : b4RawGapContribution ![0, 2, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 6] = b4GapPatternWeight 2 3 6 * 0 :=
      b4GapContribution_from_row 0 2 3 6 0 row_00_02_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_06

def layers_00_02_03_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 18, 17, 15, 12, 9, 6, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_02_03_07

theorem cells_00_02_03_07 : QTableValid (![0, 2, 5, 12] : Fin 4 → ℕ) layers_00_02_03_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_03_07

theorem valid_00_02_03_07 :
    SparseRowValid (![0, 2, 5, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_02_03_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 5, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 5 + 12 = 19
      decide
    have hzsq : (∑ i, (((![0, 2, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 173 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 5^2 + 12^2 = 173
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_03_07
#print axioms Paper7MomentGapNumeric.valid_00_02_03_07

def qvalues_00_02_03_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_03_07

theorem row_00_02_03_07 : b4RowContribution (![0, 2, 5, 12] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![0, 2, 5, 12] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_02_03_07) :=
      sparseRow_sound (![0, 2, 5, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_02_03_07) valid_00_02_03_07
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_03_07 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_03_07

theorem weighted_00_02_03_07 : b4RawGapContribution ![0, 2, 3, 7] = 432 := by
  calc
    b4RawGapContribution ![0, 2, 3, 7] = b4GapPatternWeight 2 3 7 * 18 :=
      b4GapContribution_from_row 0 2 3 7 18 row_00_02_03_07
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_07

theorem row_00_02_03_08 : b4RowContribution (![0, 2, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 13] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 13 = 20
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 13^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_08

theorem weighted_00_02_03_08 : b4RawGapContribution ![0, 2, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 8] = b4GapPatternWeight 2 3 8 * 0 :=
      b4GapContribution_from_row 0 2 3 8 0 row_00_02_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_08

def layers_00_02_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 18, 18, 18, 17, 15, 12, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_02_03_09

theorem cells_00_02_03_09 : QTableValid (![0, 2, 5, 14] : Fin 4 → ℕ) layers_00_02_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_03_09

theorem valid_00_02_03_09 :
    SparseRowValid (![0, 2, 5, 14] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_02_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 5, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 5 + 14 = 21
      decide
    have hzsq : (∑ i, (((![0, 2, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 5^2 + 14^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_03_09
#print axioms Paper7MomentGapNumeric.valid_00_02_03_09

def qvalues_00_02_03_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_03_09

theorem row_00_02_03_09 : b4RowContribution (![0, 2, 5, 14] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![0, 2, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_02_03_09) :=
      sparseRow_sound (![0, 2, 5, 14] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_02_03_09) valid_00_02_03_09
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_03_09 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_03_09

theorem weighted_00_02_03_09 : b4RawGapContribution ![0, 2, 3, 9] = 840 := by
  calc
    b4RawGapContribution ![0, 2, 3, 9] = b4GapPatternWeight 2 3 9 * 35 :=
      b4GapContribution_from_row 0 2 3 9 35 row_00_02_03_09
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_09

theorem row_00_02_03_10 : b4RowContribution (![0, 2, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 15] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 15 = 22
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 15^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_10

theorem weighted_00_02_03_10 : b4RawGapContribution ![0, 2, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 10] = b4GapPatternWeight 2 3 10 * 0 :=
      b4GapContribution_from_row 0 2 3 10 0 row_00_02_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_10

def layers_00_02_03_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_02_03_11

theorem cells_00_02_03_11 : QTableValid (![0, 2, 5, 16] : Fin 4 → ℕ) layers_00_02_03_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_03_11

theorem valid_00_02_03_11 :
    SparseRowValid (![0, 2, 5, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_03_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 5, 16] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 5 + 16 = 23
      decide
    have hzsq : (∑ i, (((![0, 2, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 5^2 + 16^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_03_11
#print axioms Paper7MomentGapNumeric.valid_00_02_03_11

def qvalues_00_02_03_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_03_11

theorem row_00_02_03_11 : b4RowContribution (![0, 2, 5, 16] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![0, 2, 5, 16] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_02_03_11) :=
      sparseRow_sound (![0, 2, 5, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_03_11) valid_00_02_03_11
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_03_11 Q := by
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
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_03_11

theorem weighted_00_02_03_11 : b4RawGapContribution ![0, 2, 3, 11] = 432 := by
  calc
    b4RawGapContribution ![0, 2, 3, 11] = b4GapPatternWeight 2 3 11 * 18 :=
      b4GapContribution_from_row 0 2 3 11 18 row_00_02_03_11
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_11

theorem row_00_02_03_12 : b4RowContribution (![0, 2, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 17 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 17^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_12

theorem weighted_00_02_03_12 : b4RawGapContribution ![0, 2, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 12] = b4GapPatternWeight 2 3 12 * 0 :=
      b4GapContribution_from_row 0 2 3 12 0 row_00_02_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_12

theorem row_00_02_03_13 : b4RowContribution (![0, 2, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 18 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 18^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_13

theorem weighted_00_02_03_13 : b4RawGapContribution ![0, 2, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 13] = b4GapPatternWeight 2 3 13 * 0 :=
      b4GapContribution_from_row 0 2 3 13 0 row_00_02_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_13

theorem row_00_02_03_14 : b4RowContribution (![0, 2, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 19 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 19^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_14

theorem weighted_00_02_03_14 : b4RawGapContribution ![0, 2, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 14] = b4GapPatternWeight 2 3 14 * 0 :=
      b4GapContribution_from_row 0 2 3 14 0 row_00_02_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_14

theorem row_00_02_03_15 : b4RowContribution (![0, 2, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 20 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 20^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_15

theorem weighted_00_02_03_15 : b4RawGapContribution ![0, 2, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 15] = b4GapPatternWeight 2 3 15 * 0 :=
      b4GapContribution_from_row 0 2 3 15 0 row_00_02_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_15

theorem row_00_02_03_16 : b4RowContribution (![0, 2, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 21 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 21^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_16

theorem weighted_00_02_03_16 : b4RawGapContribution ![0, 2, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 16] = b4GapPatternWeight 2 3 16 * 0 :=
      b4GapContribution_from_row 0 2 3 16 0 row_00_02_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_16

def layers_00_02_03_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18]]
#print axioms Paper7MomentGapNumeric.layers_00_02_03_17

theorem cells_00_02_03_17 : QTableValid (![0, 2, 5, 22] : Fin 4 → ℕ) layers_00_02_03_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_03_17

theorem valid_00_02_03_17 :
    SparseRowValid (![0, 2, 5, 22] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 5, 22] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 5 + 22 = 29
      decide
    have hzsq : (∑ i, (((![0, 2, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 5^2 + 22^2 = 513
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_03_17
#print axioms Paper7MomentGapNumeric.valid_00_02_03_17

def qvalues_00_02_03_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_03_17

theorem row_00_02_03_17 : b4RowContribution (![0, 2, 5, 22] : Fin 4 → ℕ) = 17 := by
  calc
    b4RowContribution (![0, 2, 5, 22] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_17) :=
      sparseRow_sound (![0, 2, 5, 22] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_17) valid_00_02_03_17
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_03_17 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 17 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_03_17

theorem weighted_00_02_03_17 : b4RawGapContribution ![0, 2, 3, 17] = 408 := by
  calc
    b4RawGapContribution ![0, 2, 3, 17] = b4GapPatternWeight 2 3 17 * 17 :=
      b4GapContribution_from_row 0 2 3 17 17 row_00_02_03_17
    _ = 408 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_17

def layers_00_02_03_18 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18]]
#print axioms Paper7MomentGapNumeric.layers_00_02_03_18

theorem cells_00_02_03_18 : QTableValid (![0, 2, 5, 23] : Fin 4 → ℕ) layers_00_02_03_18 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_03_18

theorem valid_00_02_03_18 :
    SparseRowValid (![0, 2, 5, 23] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_18) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 5, 23] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 5 + 23 = 30
      decide
    have hzsq : (∑ i, (((![0, 2, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 5^2 + 23^2 = 558
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_03_18
#print axioms Paper7MomentGapNumeric.valid_00_02_03_18

def qvalues_00_02_03_18 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_03_18

theorem row_00_02_03_18 : b4RowContribution (![0, 2, 5, 23] : Fin 4 → ℕ) = 17 := by
  calc
    b4RowContribution (![0, 2, 5, 23] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_18) :=
      sparseRow_sound (![0, 2, 5, 23] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_03_18) valid_00_02_03_18
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_03_18 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 17 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_03_18

theorem weighted_00_02_03_18 : b4RawGapContribution ![0, 2, 3, 18] = 408 := by
  calc
    b4RawGapContribution ![0, 2, 3, 18] = b4GapPatternWeight 2 3 18 * 17 :=
      b4GapContribution_from_row 0 2 3 18 17 row_00_02_03_18
    _ = 408 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_18

theorem row_00_02_03_19 : b4RowContribution (![0, 2, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 24 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 605 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 24^2 = 605
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_19

theorem weighted_00_02_03_19 : b4RawGapContribution ![0, 2, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 19] = b4GapPatternWeight 2 3 19 * 0 :=
      b4GapContribution_from_row 0 2 3 19 0 row_00_02_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_19

theorem row_00_02_03_20 : b4RowContribution (![0, 2, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 25 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 654 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 25^2 = 654
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_20

theorem weighted_00_02_03_20 : b4RawGapContribution ![0, 2, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 20] = b4GapPatternWeight 2 3 20 * 0 :=
      b4GapContribution_from_row 0 2 3 20 0 row_00_02_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_20

theorem row_00_02_03_21 : b4RowContribution (![0, 2, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 26 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 705 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 26^2 = 705
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_21

theorem weighted_00_02_03_21 : b4RawGapContribution ![0, 2, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 21] = b4GapPatternWeight 2 3 21 * 0 :=
      b4GapContribution_from_row 0 2 3 21 0 row_00_02_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_21

theorem row_00_02_03_22 : b4RowContribution (![0, 2, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 27 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 758 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 27^2 = 758
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_22

theorem weighted_00_02_03_22 : b4RawGapContribution ![0, 2, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 22] = b4GapPatternWeight 2 3 22 * 0 :=
      b4GapContribution_from_row 0 2 3 22 0 row_00_02_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_22

theorem row_00_02_03_23 : b4RowContribution (![0, 2, 5, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 28 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 813 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 28^2 = 813
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_23

theorem weighted_00_02_03_23 : b4RawGapContribution ![0, 2, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 23] = b4GapPatternWeight 2 3 23 * 0 :=
      b4GapContribution_from_row 0 2 3 23 0 row_00_02_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_23

theorem row_00_02_03_24 : b4RowContribution (![0, 2, 5, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 29 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 870 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 29^2 = 870
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_24

theorem weighted_00_02_03_24 : b4RawGapContribution ![0, 2, 3, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 24] = b4GapPatternWeight 2 3 24 * 0 :=
      b4GapContribution_from_row 0 2 3 24 0 row_00_02_03_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_24

theorem row_00_02_03_25 : b4RowContribution (![0, 2, 5, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 5, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 5 + 30 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 5, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 929 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 5^2 + 30^2 = 929
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_03_25

theorem weighted_00_02_03_25 : b4RawGapContribution ![0, 2, 3, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 3, 25] = b4GapPatternWeight 2 3 25 * 0 :=
      b4GapContribution_from_row 0 2 3 25 0 row_00_02_03_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_03_25

def dvalues_00_02_03 : Fin 26 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 432, 0, 840, 0, 432, 0, 0, 0, 0, 0, 408, 408, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_03

theorem dblock_00_02_03 : b4GapPatternDBlock 0 2 3 = 2520 := by
  calc
    b4GapPatternDBlock 0 2 3 = ∑ d : Fin 26, dvalues_00_02_03 d := by
      apply b4GapDBlock_of_rows 0 2 3 dvalues_00_02_03
      intro d
      fin_cases d
      · exact weighted_00_02_03_00
      · exact weighted_00_02_03_01
      · exact weighted_00_02_03_02
      · exact weighted_00_02_03_03
      · exact weighted_00_02_03_04
      · exact weighted_00_02_03_05
      · exact weighted_00_02_03_06
      · exact weighted_00_02_03_07
      · exact weighted_00_02_03_08
      · exact weighted_00_02_03_09
      · exact weighted_00_02_03_10
      · exact weighted_00_02_03_11
      · exact weighted_00_02_03_12
      · exact weighted_00_02_03_13
      · exact weighted_00_02_03_14
      · exact weighted_00_02_03_15
      · exact weighted_00_02_03_16
      · exact weighted_00_02_03_17
      · exact weighted_00_02_03_18
      · exact weighted_00_02_03_19
      · exact weighted_00_02_03_20
      · exact weighted_00_02_03_21
      · exact weighted_00_02_03_22
      · exact weighted_00_02_03_23
      · exact weighted_00_02_03_24
      · exact weighted_00_02_03_25
    _ = 2520 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_03

end Paper7MomentGapNumeric
