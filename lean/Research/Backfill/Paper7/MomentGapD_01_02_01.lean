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

def layers_01_02_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 30, 32, 30, 24, 16, 9, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_02_01_00

theorem cells_01_02_01_00 : QTableValid (![1, 3, 4, 4] : Fin 4 → ℕ) layers_01_02_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_01_00

theorem valid_01_02_01_00 :
    SparseRowValid (![1, 3, 4, 4] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_02_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 4, 4] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 4 + 4 = 12
      decide
    have hzsq : (∑ i, (((![1, 3, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 42 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 4^2 + 4^2 = 42
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_01_00
#print axioms Paper7MomentGapNumeric.valid_01_02_01_00

def qvalues_01_02_01_00 : Fin 19 → ℕ := ![0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_01_00

theorem row_01_02_01_00 : b4RowContribution (![1, 3, 4, 4] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 3, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_02_01_00) :=
      sparseRow_sound (![1, 3, 4, 4] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_02_01_00) valid_01_02_01_00
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_01_00 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_01_00

theorem weighted_01_02_01_00 : b4RawGapContribution ![1, 2, 1, 0] = 192 := by
  calc
    b4RawGapContribution ![1, 2, 1, 0] = b4GapPatternWeight 2 1 0 * 16 :=
      b4GapContribution_from_row 1 2 1 0 16 row_01_02_01_00
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_00

theorem row_01_02_01_01 : b4RowContribution (![1, 3, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 5 = 13
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 51 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 5^2 = 51
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_01

theorem weighted_01_02_01_01 : b4RawGapContribution ![1, 2, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 1] = b4GapPatternWeight 2 1 1 * 0 :=
      b4GapContribution_from_row 1 2 1 1 0 row_01_02_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_01

theorem row_01_02_01_02 : b4RowContribution (![1, 3, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 6 = 14
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 62 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 6^2 = 62
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_02

theorem weighted_01_02_01_02 : b4RawGapContribution ![1, 2, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 2] = b4GapPatternWeight 2 1 2 * 0 :=
      b4GapContribution_from_row 1 2 1 2 0 row_01_02_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_02

theorem row_01_02_01_03 : b4RowContribution (![1, 3, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 7 = 15
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 75 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 7^2 = 75
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_03

theorem weighted_01_02_01_03 : b4RawGapContribution ![1, 2, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 3] = b4GapPatternWeight 2 1 3 * 0 :=
      b4GapContribution_from_row 1 2 1 3 0 row_01_02_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_03

theorem row_01_02_01_04 : b4RowContribution (![1, 3, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 8 = 16
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 90 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 8^2 = 90
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_04

theorem weighted_01_02_01_04 : b4RawGapContribution ![1, 2, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 4] = b4GapPatternWeight 2 1 4 * 0 :=
      b4GapContribution_from_row 1 2 1 4 0 row_01_02_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_04

theorem row_01_02_01_05 : b4RowContribution (![1, 3, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 9 = 17
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 107 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 9^2 = 107
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_05

theorem weighted_01_02_01_05 : b4RawGapContribution ![1, 2, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 5] = b4GapPatternWeight 2 1 5 * 0 :=
      b4GapContribution_from_row 1 2 1 5 0 row_01_02_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_05

theorem row_01_02_01_06 : b4RowContribution (![1, 3, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 10 = 18
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 10^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_06

theorem weighted_01_02_01_06 : b4RawGapContribution ![1, 2, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 6] = b4GapPatternWeight 2 1 6 * 0 :=
      b4GapContribution_from_row 1 2 1 6 0 row_01_02_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_06

theorem row_01_02_01_07 : b4RowContribution (![1, 3, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 11] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 11 = 19
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 147 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 11^2 = 147
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_07

theorem weighted_01_02_01_07 : b4RawGapContribution ![1, 2, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 7] = b4GapPatternWeight 2 1 7 * 0 :=
      b4GapContribution_from_row 1 2 1 7 0 row_01_02_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_07

def layers_01_02_01_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 31, 36, 39, 40, 40, 40, 40, 40, 39, 36, 31, 24, 16, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_02_01_08

theorem cells_01_02_01_08 : QTableValid (![1, 3, 4, 12] : Fin 4 → ℕ) layers_01_02_01_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_01_08

theorem valid_01_02_01_08 :
    SparseRowValid (![1, 3, 4, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_01_02_01_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 4, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 4 + 12 = 20
      decide
    have hzsq : (∑ i, (((![1, 3, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 4^2 + 12^2 = 170
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_01_08
#print axioms Paper7MomentGapNumeric.valid_01_02_01_08

def qvalues_01_02_01_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_01_08

theorem row_01_02_01_08 : b4RowContribution (![1, 3, 4, 12] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 3, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_01_02_01_08) :=
      sparseRow_sound (![1, 3, 4, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_01_02_01_08) valid_01_02_01_08
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_01_08 Q := by
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
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_01_08

theorem weighted_01_02_01_08 : b4RawGapContribution ![1, 2, 1, 8] = 960 := by
  calc
    b4RawGapContribution ![1, 2, 1, 8] = b4GapPatternWeight 2 1 8 * 40 :=
      b4GapContribution_from_row 1 2 1 8 40 row_01_02_01_08
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_08

theorem row_01_02_01_09 : b4RowContribution (![1, 3, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 13] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 13 = 21
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 13^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_09

theorem weighted_01_02_01_09 : b4RawGapContribution ![1, 2, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 9] = b4GapPatternWeight 2 1 9 * 0 :=
      b4GapContribution_from_row 1 2 1 9 0 row_01_02_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_09

def layers_01_02_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 31, 36, 39, 40, 40, 40, 40, 40, 40, 40, 39, 36, 31, 24]]
#print axioms Paper7MomentGapNumeric.layers_01_02_01_10

theorem cells_01_02_01_10 : QTableValid (![1, 3, 4, 14] : Fin 4 → ℕ) layers_01_02_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_01_10

theorem valid_01_02_01_10 :
    SparseRowValid (![1, 3, 4, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_02_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 4, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 4 + 14 = 22
      decide
    have hzsq : (∑ i, (((![1, 3, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 4^2 + 14^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_01_10
#print axioms Paper7MomentGapNumeric.valid_01_02_01_10

def qvalues_01_02_01_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_01_10

theorem row_01_02_01_10 : b4RowContribution (![1, 3, 4, 14] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 3, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_01_02_01_10) :=
      sparseRow_sound (![1, 3, 4, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_02_01_10) valid_01_02_01_10
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_01_10 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_01_10

theorem weighted_01_02_01_10 : b4RawGapContribution ![1, 2, 1, 10] = 960 := by
  calc
    b4RawGapContribution ![1, 2, 1, 10] = b4GapPatternWeight 2 1 10 * 40 :=
      b4GapContribution_from_row 1 2 1 10 40 row_01_02_01_10
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_10

theorem row_01_02_01_11 : b4RowContribution (![1, 3, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 15 = 23
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 15^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_11

theorem weighted_01_02_01_11 : b4RawGapContribution ![1, 2, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 11] = b4GapPatternWeight 2 1 11 * 0 :=
      b4GapContribution_from_row 1 2 1 11 0 row_01_02_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_11

def layers_01_02_01_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 31, 36, 39, 40, 40, 40, 40, 40, 40, 40, 40, 40, 39, 36]]
#print axioms Paper7MomentGapNumeric.layers_01_02_01_12

theorem cells_01_02_01_12 : QTableValid (![1, 3, 4, 16] : Fin 4 → ℕ) layers_01_02_01_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_01_12

theorem valid_01_02_01_12 :
    SparseRowValid (![1, 3, 4, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_02_01_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 4, 16] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 4 + 16 = 24
      decide
    have hzsq : (∑ i, (((![1, 3, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 4^2 + 16^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_01_12
#print axioms Paper7MomentGapNumeric.valid_01_02_01_12

def qvalues_01_02_01_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_01_12

theorem row_01_02_01_12 : b4RowContribution (![1, 3, 4, 16] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 3, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_02_01_12) :=
      sparseRow_sound (![1, 3, 4, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_02_01_12) valid_01_02_01_12
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_01_12 Q := by
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
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_01_12

theorem weighted_01_02_01_12 : b4RawGapContribution ![1, 2, 1, 12] = 960 := by
  calc
    b4RawGapContribution ![1, 2, 1, 12] = b4GapPatternWeight 2 1 12 * 40 :=
      b4GapContribution_from_row 1 2 1 12 40 row_01_02_01_12
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_12

theorem row_01_02_01_13 : b4RowContribution (![1, 3, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 17 = 25
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 17^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_13

theorem weighted_01_02_01_13 : b4RawGapContribution ![1, 2, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 13] = b4GapPatternWeight 2 1 13 * 0 :=
      b4GapContribution_from_row 1 2 1 13 0 row_01_02_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_13

theorem row_01_02_01_14 : b4RowContribution (![1, 3, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 18 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 18^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_14

theorem weighted_01_02_01_14 : b4RawGapContribution ![1, 2, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 14] = b4GapPatternWeight 2 1 14 * 0 :=
      b4GapContribution_from_row 1 2 1 14 0 row_01_02_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_14

theorem row_01_02_01_15 : b4RowContribution (![1, 3, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 19 = 27
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 19^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_15

theorem weighted_01_02_01_15 : b4RawGapContribution ![1, 2, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 15] = b4GapPatternWeight 2 1 15 * 0 :=
      b4GapContribution_from_row 1 2 1 15 0 row_01_02_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_15

theorem row_01_02_01_16 : b4RowContribution (![1, 3, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 20 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 20^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_16

theorem weighted_01_02_01_16 : b4RawGapContribution ![1, 2, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 16] = b4GapPatternWeight 2 1 16 * 0 :=
      b4GapContribution_from_row 1 2 1 16 0 row_01_02_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_16

theorem row_01_02_01_17 : b4RowContribution (![1, 3, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 21 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 467 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 21^2 = 467
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_17

theorem weighted_01_02_01_17 : b4RawGapContribution ![1, 2, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 17] = b4GapPatternWeight 2 1 17 * 0 :=
      b4GapContribution_from_row 1 2 1 17 0 row_01_02_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_17

theorem row_01_02_01_18 : b4RowContribution (![1, 3, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 22 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 22^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_18

theorem weighted_01_02_01_18 : b4RawGapContribution ![1, 2, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 18] = b4GapPatternWeight 2 1 18 * 0 :=
      b4GapContribution_from_row 1 2 1 18 0 row_01_02_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_18

theorem row_01_02_01_19 : b4RowContribution (![1, 3, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 23 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 555 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 23^2 = 555
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_19

theorem weighted_01_02_01_19 : b4RawGapContribution ![1, 2, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 19] = b4GapPatternWeight 2 1 19 * 0 :=
      b4GapContribution_from_row 1 2 1 19 0 row_01_02_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_19

theorem row_01_02_01_20 : b4RowContribution (![1, 3, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 24 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 602 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 24^2 = 602
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_20

theorem weighted_01_02_01_20 : b4RawGapContribution ![1, 2, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 20] = b4GapPatternWeight 2 1 20 * 0 :=
      b4GapContribution_from_row 1 2 1 20 0 row_01_02_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_20

theorem row_01_02_01_21 : b4RowContribution (![1, 3, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 25 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 651 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 25^2 = 651
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_21

theorem weighted_01_02_01_21 : b4RawGapContribution ![1, 2, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 21] = b4GapPatternWeight 2 1 21 * 0 :=
      b4GapContribution_from_row 1 2 1 21 0 row_01_02_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_21

theorem row_01_02_01_22 : b4RowContribution (![1, 3, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 26 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 702 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 26^2 = 702
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_22

theorem weighted_01_02_01_22 : b4RawGapContribution ![1, 2, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 22] = b4GapPatternWeight 2 1 22 * 0 :=
      b4GapContribution_from_row 1 2 1 22 0 row_01_02_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_22

theorem row_01_02_01_23 : b4RowContribution (![1, 3, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 27 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 755 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 27^2 = 755
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_23

theorem weighted_01_02_01_23 : b4RawGapContribution ![1, 2, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 23] = b4GapPatternWeight 2 1 23 * 0 :=
      b4GapContribution_from_row 1 2 1 23 0 row_01_02_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_23

theorem row_01_02_01_24 : b4RowContribution (![1, 3, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 28 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 810 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 28^2 = 810
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_24

theorem weighted_01_02_01_24 : b4RawGapContribution ![1, 2, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 24] = b4GapPatternWeight 2 1 24 * 0 :=
      b4GapContribution_from_row 1 2 1 24 0 row_01_02_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_24

theorem row_01_02_01_25 : b4RowContribution (![1, 3, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 4, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 4 + 29 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 867 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 4^2 + 29^2 = 867
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_01_25

theorem weighted_01_02_01_25 : b4RawGapContribution ![1, 2, 1, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 1, 25] = b4GapPatternWeight 2 1 25 * 0 :=
      b4GapContribution_from_row 1 2 1 25 0 row_01_02_01_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_01_25

def dvalues_01_02_01 : Fin 26 → ℕ := ![192, 0, 0, 0, 0, 0, 0, 0, 960, 0, 960, 0, 960, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_01

theorem dblock_01_02_01 : b4GapPatternDBlock 1 2 1 = 3072 := by
  calc
    b4GapPatternDBlock 1 2 1 = ∑ d : Fin 26, dvalues_01_02_01 d := by
      apply b4GapDBlock_of_rows 1 2 1 dvalues_01_02_01
      intro d
      fin_cases d
      · exact weighted_01_02_01_00
      · exact weighted_01_02_01_01
      · exact weighted_01_02_01_02
      · exact weighted_01_02_01_03
      · exact weighted_01_02_01_04
      · exact weighted_01_02_01_05
      · exact weighted_01_02_01_06
      · exact weighted_01_02_01_07
      · exact weighted_01_02_01_08
      · exact weighted_01_02_01_09
      · exact weighted_01_02_01_10
      · exact weighted_01_02_01_11
      · exact weighted_01_02_01_12
      · exact weighted_01_02_01_13
      · exact weighted_01_02_01_14
      · exact weighted_01_02_01_15
      · exact weighted_01_02_01_16
      · exact weighted_01_02_01_17
      · exact weighted_01_02_01_18
      · exact weighted_01_02_01_19
      · exact weighted_01_02_01_20
      · exact weighted_01_02_01_21
      · exact weighted_01_02_01_22
      · exact weighted_01_02_01_23
      · exact weighted_01_02_01_24
      · exact weighted_01_02_01_25
    _ = 3072 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_01

end Paper7MomentGapNumeric
