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

theorem row_01_04_00_00 : b4RowContribution (![1, 5, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 5] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 5 = 16
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 76 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 5^2 = 76
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_00

theorem weighted_01_04_00_00 : b4RawGapContribution ![1, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 1 4 0 0 0 row_01_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_00

theorem row_01_04_00_01 : b4RowContribution (![1, 5, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 6] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 6 = 17
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 87 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 6^2 = 87
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_01

theorem weighted_01_04_00_01 : b4RawGapContribution ![1, 4, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 0 :=
      b4GapContribution_from_row 1 4 0 1 0 row_01_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_01

theorem row_01_04_00_02 : b4RowContribution (![1, 5, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 7 = 18
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 7^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_02

theorem weighted_01_04_00_02 : b4RawGapContribution ![1, 4, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 2] = b4GapPatternWeight 4 0 2 * 0 :=
      b4GapContribution_from_row 1 4 0 2 0 row_01_04_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_02

theorem row_01_04_00_03 : b4RowContribution (![1, 5, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 8 = 19
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 115 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 8^2 = 115
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_03

theorem weighted_01_04_00_03 : b4RawGapContribution ![1, 4, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 3] = b4GapPatternWeight 4 0 3 * 0 :=
      b4GapContribution_from_row 1 4 0 3 0 row_01_04_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_03

theorem row_01_04_00_04 : b4RowContribution (![1, 5, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 9 = 20
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 9^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_04

theorem weighted_01_04_00_04 : b4RawGapContribution ![1, 4, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 4] = b4GapPatternWeight 4 0 4 * 0 :=
      b4GapContribution_from_row 1 4 0 4 0 row_01_04_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_04

theorem row_01_04_00_05 : b4RowContribution (![1, 5, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 10 = 21
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 151 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 10^2 = 151
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_05

theorem weighted_01_04_00_05 : b4RawGapContribution ![1, 4, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 5] = b4GapPatternWeight 4 0 5 * 0 :=
      b4GapContribution_from_row 1 4 0 5 0 row_01_04_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_05

theorem row_01_04_00_06 : b4RowContribution (![1, 5, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 11 = 22
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 11^2 = 172
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_06

theorem weighted_01_04_00_06 : b4RawGapContribution ![1, 4, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 6] = b4GapPatternWeight 4 0 6 * 0 :=
      b4GapContribution_from_row 1 4 0 6 0 row_01_04_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_06

theorem row_01_04_00_07 : b4RowContribution (![1, 5, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 12 = 23
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 12^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_07

theorem weighted_01_04_00_07 : b4RawGapContribution ![1, 4, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 7] = b4GapPatternWeight 4 0 7 * 0 :=
      b4GapContribution_from_row 1 4 0 7 0 row_01_04_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_07

def layers_01_04_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 47, 56, 63, 68, 71, 72, 72, 72, 71, 68, 63, 56, 47]]
#print axioms Paper7MomentGapNumeric.layers_01_04_00_08

theorem cells_01_04_00_08 : QTableValid (![1, 5, 5, 13] : Fin 4 → ℕ) layers_01_04_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_00_08

theorem valid_01_04_00_08 :
    SparseRowValid (![1, 5, 5, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 5, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 5 + 13 = 24
      decide
    have hzsq : (∑ i, (((![1, 5, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 5^2 + 13^2 = 220
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_00_08
#print axioms Paper7MomentGapNumeric.valid_01_04_00_08

def qvalues_01_04_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_00_08

theorem row_01_04_00_08 : b4RowContribution (![1, 5, 5, 13] : Fin 4 → ℕ) = 71 := by
  calc
    b4RowContribution (![1, 5, 5, 13] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_04_00_08) :=
      sparseRow_sound (![1, 5, 5, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_00_08) valid_01_04_00_08
    _ = 71 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_00_08 Q := by
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
        _ = 71 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_00_08

theorem weighted_01_04_00_08 : b4RawGapContribution ![1, 4, 0, 8] = 852 := by
  calc
    b4RawGapContribution ![1, 4, 0, 8] = b4GapPatternWeight 4 0 8 * 71 :=
      b4GapContribution_from_row 1 4 0 8 71 row_01_04_00_08
    _ = 852 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_08

theorem row_01_04_00_09 : b4RowContribution (![1, 5, 5, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 14 = 25
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 14^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_09

theorem weighted_01_04_00_09 : b4RawGapContribution ![1, 4, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 9] = b4GapPatternWeight 4 0 9 * 0 :=
      b4GapContribution_from_row 1 4 0 9 0 row_01_04_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_09

def layers_01_04_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 47, 56, 63, 68, 71, 72, 72, 72, 72, 72, 71, 68, 63]]
#print axioms Paper7MomentGapNumeric.layers_01_04_00_10

theorem cells_01_04_00_10 : QTableValid (![1, 5, 5, 15] : Fin 4 → ℕ) layers_01_04_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_00_10

theorem valid_01_04_00_10 :
    SparseRowValid (![1, 5, 5, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 5, 15] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 5 + 15 = 26
      decide
    have hzsq : (∑ i, (((![1, 5, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 5^2 + 15^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_00_10
#print axioms Paper7MomentGapNumeric.valid_01_04_00_10

def qvalues_01_04_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_00_10

theorem row_01_04_00_10 : b4RowContribution (![1, 5, 5, 15] : Fin 4 → ℕ) = 68 := by
  calc
    b4RowContribution (![1, 5, 5, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_04_00_10) :=
      sparseRow_sound (![1, 5, 5, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_00_10) valid_01_04_00_10
    _ = 68 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_00_10 Q := by
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
        _ = 68 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_00_10

theorem weighted_01_04_00_10 : b4RawGapContribution ![1, 4, 0, 10] = 816 := by
  calc
    b4RawGapContribution ![1, 4, 0, 10] = b4GapPatternWeight 4 0 10 * 68 :=
      b4GapContribution_from_row 1 4 0 10 68 row_01_04_00_10
    _ = 816 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_10

theorem row_01_04_00_11 : b4RowContribution (![1, 5, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 16 = 27
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 16^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_11

theorem weighted_01_04_00_11 : b4RawGapContribution ![1, 4, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 11] = b4GapPatternWeight 4 0 11 * 0 :=
      b4GapContribution_from_row 1 4 0 11 0 row_01_04_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_11

theorem row_01_04_00_12 : b4RowContribution (![1, 5, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 17 = 28
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 17^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_12

theorem weighted_01_04_00_12 : b4RawGapContribution ![1, 4, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 12] = b4GapPatternWeight 4 0 12 * 0 :=
      b4GapContribution_from_row 1 4 0 12 0 row_01_04_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_12

theorem row_01_04_00_13 : b4RowContribution (![1, 5, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 18 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 18^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_13

theorem weighted_01_04_00_13 : b4RawGapContribution ![1, 4, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 13] = b4GapPatternWeight 4 0 13 * 0 :=
      b4GapContribution_from_row 1 4 0 13 0 row_01_04_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_13

theorem row_01_04_00_14 : b4RowContribution (![1, 5, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 19 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 412 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 19^2 = 412
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_14

theorem weighted_01_04_00_14 : b4RawGapContribution ![1, 4, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 14] = b4GapPatternWeight 4 0 14 * 0 :=
      b4GapContribution_from_row 1 4 0 14 0 row_01_04_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_14

theorem row_01_04_00_15 : b4RowContribution (![1, 5, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 20 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 20^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_15

theorem weighted_01_04_00_15 : b4RawGapContribution ![1, 4, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 15] = b4GapPatternWeight 4 0 15 * 0 :=
      b4GapContribution_from_row 1 4 0 15 0 row_01_04_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_15

theorem row_01_04_00_16 : b4RowContribution (![1, 5, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 21 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 492 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 21^2 = 492
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_16

theorem weighted_01_04_00_16 : b4RawGapContribution ![1, 4, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 16] = b4GapPatternWeight 4 0 16 * 0 :=
      b4GapContribution_from_row 1 4 0 16 0 row_01_04_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_16

theorem row_01_04_00_17 : b4RowContribution (![1, 5, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 22 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 535 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 22^2 = 535
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_17

theorem weighted_01_04_00_17 : b4RawGapContribution ![1, 4, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 17] = b4GapPatternWeight 4 0 17 * 0 :=
      b4GapContribution_from_row 1 4 0 17 0 row_01_04_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_17

theorem row_01_04_00_18 : b4RowContribution (![1, 5, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 23 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 580 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 23^2 = 580
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_18

theorem weighted_01_04_00_18 : b4RawGapContribution ![1, 4, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 18] = b4GapPatternWeight 4 0 18 * 0 :=
      b4GapContribution_from_row 1 4 0 18 0 row_01_04_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_18

theorem row_01_04_00_19 : b4RowContribution (![1, 5, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 24 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 627 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 24^2 = 627
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_19

theorem weighted_01_04_00_19 : b4RawGapContribution ![1, 4, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 19] = b4GapPatternWeight 4 0 19 * 0 :=
      b4GapContribution_from_row 1 4 0 19 0 row_01_04_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_19

theorem row_01_04_00_20 : b4RowContribution (![1, 5, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 25 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 676 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 25^2 = 676
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_20

theorem weighted_01_04_00_20 : b4RawGapContribution ![1, 4, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 20] = b4GapPatternWeight 4 0 20 * 0 :=
      b4GapContribution_from_row 1 4 0 20 0 row_01_04_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_20

theorem row_01_04_00_21 : b4RowContribution (![1, 5, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 5, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 5 + 26 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 727 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 5^2 + 26^2 = 727
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_00_21

theorem weighted_01_04_00_21 : b4RawGapContribution ![1, 4, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 0, 21] = b4GapPatternWeight 4 0 21 * 0 :=
      b4GapContribution_from_row 1 4 0 21 0 row_01_04_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_00_21

def dvalues_01_04_00 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 852, 0, 816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_00

theorem dblock_01_04_00 : b4GapPatternDBlock 1 4 0 = 1668 := by
  calc
    b4GapPatternDBlock 1 4 0 = ∑ d : Fin 22, dvalues_01_04_00 d := by
      apply b4GapDBlock_of_rows 1 4 0 dvalues_01_04_00
      intro d
      fin_cases d
      · exact weighted_01_04_00_00
      · exact weighted_01_04_00_01
      · exact weighted_01_04_00_02
      · exact weighted_01_04_00_03
      · exact weighted_01_04_00_04
      · exact weighted_01_04_00_05
      · exact weighted_01_04_00_06
      · exact weighted_01_04_00_07
      · exact weighted_01_04_00_08
      · exact weighted_01_04_00_09
      · exact weighted_01_04_00_10
      · exact weighted_01_04_00_11
      · exact weighted_01_04_00_12
      · exact weighted_01_04_00_13
      · exact weighted_01_04_00_14
      · exact weighted_01_04_00_15
      · exact weighted_01_04_00_16
      · exact weighted_01_04_00_17
      · exact weighted_01_04_00_18
      · exact weighted_01_04_00_19
      · exact weighted_01_04_00_20
      · exact weighted_01_04_00_21
    _ = 1668 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_00

end Paper7MomentGapNumeric
