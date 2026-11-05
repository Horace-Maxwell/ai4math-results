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

theorem row_01_02_03_00 : b4RowContribution (![1, 3, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 6 = 16
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 6^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_00

theorem weighted_01_02_03_00 : b4RawGapContribution ![1, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 1 2 3 0 0 row_01_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_00

theorem row_01_02_03_01 : b4RowContribution (![1, 3, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 7 = 17
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 95 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 7^2 = 95
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_01

theorem weighted_01_02_03_01 : b4RawGapContribution ![1, 2, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 0 :=
      b4GapContribution_from_row 1 2 3 1 0 row_01_02_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_01

theorem row_01_02_03_02 : b4RowContribution (![1, 3, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 8 = 18
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 110 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 8^2 = 110
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_02

theorem weighted_01_02_03_02 : b4RawGapContribution ![1, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 1 2 3 2 0 row_01_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_02

theorem row_01_02_03_03 : b4RowContribution (![1, 3, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 9 = 19
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 127 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 9^2 = 127
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_03

theorem weighted_01_02_03_03 : b4RawGapContribution ![1, 2, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 0 :=
      b4GapContribution_from_row 1 2 3 3 0 row_01_02_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_03

theorem row_01_02_03_04 : b4RowContribution (![1, 3, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 10 = 20
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 10^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_04

theorem weighted_01_02_03_04 : b4RawGapContribution ![1, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 1 2 3 4 0 row_01_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_04

theorem row_01_02_03_05 : b4RowContribution (![1, 3, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 11 = 21
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 167 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 11^2 = 167
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_05

theorem weighted_01_02_03_05 : b4RawGapContribution ![1, 2, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 0 :=
      b4GapContribution_from_row 1 2 3 5 0 row_01_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_05

theorem row_01_02_03_06 : b4RowContribution (![1, 3, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 12 = 22
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 12^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_06

theorem weighted_01_02_03_06 : b4RawGapContribution ![1, 2, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 6] = b4GapPatternWeight 2 3 6 * 0 :=
      b4GapContribution_from_row 1 2 3 6 0 row_01_02_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_06

def layers_01_02_03_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 47, 52, 55, 56, 56, 56, 56, 55, 52, 47, 40, 32]]
#print axioms Paper7MomentGapNumeric.layers_01_02_03_07

theorem cells_01_02_03_07 : QTableValid (![1, 3, 6, 13] : Fin 4 → ℕ) layers_01_02_03_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_03_07

theorem valid_01_02_03_07 :
    SparseRowValid (![1, 3, 6, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_02_03_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 6, 13] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 6 + 13 = 23
      decide
    have hzsq : (∑ i, (((![1, 3, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 6^2 + 13^2 = 215
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_03_07
#print axioms Paper7MomentGapNumeric.valid_01_02_03_07

def qvalues_01_02_03_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_03_07

theorem row_01_02_03_07 : b4RowContribution (![1, 3, 6, 13] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![1, 3, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_01_02_03_07) :=
      sparseRow_sound (![1, 3, 6, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_02_03_07) valid_01_02_03_07
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_03_07 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_03_07

theorem weighted_01_02_03_07 : b4RawGapContribution ![1, 2, 3, 7] = 1320 := by
  calc
    b4RawGapContribution ![1, 2, 3, 7] = b4GapPatternWeight 2 3 7 * 55 :=
      b4GapContribution_from_row 1 2 3 7 55 row_01_02_03_07
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_07

def layers_01_02_03_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 47, 52, 55, 56, 56, 56, 56, 56, 55, 52, 47, 40]]
#print axioms Paper7MomentGapNumeric.layers_01_02_03_08

theorem cells_01_02_03_08 : QTableValid (![1, 3, 6, 14] : Fin 4 → ℕ) layers_01_02_03_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_03_08

theorem valid_01_02_03_08 :
    SparseRowValid (![1, 3, 6, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_02_03_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 6, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 6 + 14 = 24
      decide
    have hzsq : (∑ i, (((![1, 3, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 6^2 + 14^2 = 242
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_03_08
#print axioms Paper7MomentGapNumeric.valid_01_02_03_08

def qvalues_01_02_03_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_03_08

theorem row_01_02_03_08 : b4RowContribution (![1, 3, 6, 14] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 3, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_02_03_08) :=
      sparseRow_sound (![1, 3, 6, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_02_03_08) valid_01_02_03_08
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_03_08 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_03_08

theorem weighted_01_02_03_08 : b4RawGapContribution ![1, 2, 3, 8] = 768 := by
  calc
    b4RawGapContribution ![1, 2, 3, 8] = b4GapPatternWeight 2 3 8 * 32 :=
      b4GapContribution_from_row 1 2 3 8 32 row_01_02_03_08
    _ = 768 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_08

theorem row_01_02_03_09 : b4RowContribution (![1, 3, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 15 = 25
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 15^2 = 271
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_09

theorem weighted_01_02_03_09 : b4RawGapContribution ![1, 2, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 9] = b4GapPatternWeight 2 3 9 * 0 :=
      b4GapContribution_from_row 1 2 3 9 0 row_01_02_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_09

theorem row_01_02_03_10 : b4RowContribution (![1, 3, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 16 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 16^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_10

theorem weighted_01_02_03_10 : b4RawGapContribution ![1, 2, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 10] = b4GapPatternWeight 2 3 10 * 0 :=
      b4GapContribution_from_row 1 2 3 10 0 row_01_02_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_10

theorem row_01_02_03_11 : b4RowContribution (![1, 3, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 17 = 27
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 17^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_11

theorem weighted_01_02_03_11 : b4RawGapContribution ![1, 2, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 11] = b4GapPatternWeight 2 3 11 * 0 :=
      b4GapContribution_from_row 1 2 3 11 0 row_01_02_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_11

theorem row_01_02_03_12 : b4RowContribution (![1, 3, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 18 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 18^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_12

theorem weighted_01_02_03_12 : b4RawGapContribution ![1, 2, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 12] = b4GapPatternWeight 2 3 12 * 0 :=
      b4GapContribution_from_row 1 2 3 12 0 row_01_02_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_12

theorem row_01_02_03_13 : b4RowContribution (![1, 3, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 19 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 407 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 19^2 = 407
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_13

theorem weighted_01_02_03_13 : b4RawGapContribution ![1, 2, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 13] = b4GapPatternWeight 2 3 13 * 0 :=
      b4GapContribution_from_row 1 2 3 13 0 row_01_02_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_13

theorem row_01_02_03_14 : b4RowContribution (![1, 3, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 20 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 20^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_14

theorem weighted_01_02_03_14 : b4RawGapContribution ![1, 2, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 14] = b4GapPatternWeight 2 3 14 * 0 :=
      b4GapContribution_from_row 1 2 3 14 0 row_01_02_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_14

theorem row_01_02_03_15 : b4RowContribution (![1, 3, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 21 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 21^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_15

theorem weighted_01_02_03_15 : b4RawGapContribution ![1, 2, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 15] = b4GapPatternWeight 2 3 15 * 0 :=
      b4GapContribution_from_row 1 2 3 15 0 row_01_02_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_15

theorem row_01_02_03_16 : b4RowContribution (![1, 3, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 22 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 22^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_16

theorem weighted_01_02_03_16 : b4RawGapContribution ![1, 2, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 16] = b4GapPatternWeight 2 3 16 * 0 :=
      b4GapContribution_from_row 1 2 3 16 0 row_01_02_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_16

theorem row_01_02_03_17 : b4RowContribution (![1, 3, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 23 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 575 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 23^2 = 575
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_17

theorem weighted_01_02_03_17 : b4RawGapContribution ![1, 2, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 17] = b4GapPatternWeight 2 3 17 * 0 :=
      b4GapContribution_from_row 1 2 3 17 0 row_01_02_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_17

theorem row_01_02_03_18 : b4RowContribution (![1, 3, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 24 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 622 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 24^2 = 622
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_18

theorem weighted_01_02_03_18 : b4RawGapContribution ![1, 2, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 18] = b4GapPatternWeight 2 3 18 * 0 :=
      b4GapContribution_from_row 1 2 3 18 0 row_01_02_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_18

theorem row_01_02_03_19 : b4RowContribution (![1, 3, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 25 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 671 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 25^2 = 671
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_19

theorem weighted_01_02_03_19 : b4RawGapContribution ![1, 2, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 19] = b4GapPatternWeight 2 3 19 * 0 :=
      b4GapContribution_from_row 1 2 3 19 0 row_01_02_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_19

theorem row_01_02_03_20 : b4RowContribution (![1, 3, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 26 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 722 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 26^2 = 722
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_20

theorem weighted_01_02_03_20 : b4RawGapContribution ![1, 2, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 20] = b4GapPatternWeight 2 3 20 * 0 :=
      b4GapContribution_from_row 1 2 3 20 0 row_01_02_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_20

theorem row_01_02_03_21 : b4RowContribution (![1, 3, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 6, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 6 + 27 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 775 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 6^2 + 27^2 = 775
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_03_21

theorem weighted_01_02_03_21 : b4RawGapContribution ![1, 2, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 3, 21] = b4GapPatternWeight 2 3 21 * 0 :=
      b4GapContribution_from_row 1 2 3 21 0 row_01_02_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_03_21

def dvalues_01_02_03 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1320, 768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_03

theorem dblock_01_02_03 : b4GapPatternDBlock 1 2 3 = 2088 := by
  calc
    b4GapPatternDBlock 1 2 3 = ∑ d : Fin 22, dvalues_01_02_03 d := by
      apply b4GapDBlock_of_rows 1 2 3 dvalues_01_02_03
      intro d
      fin_cases d
      · exact weighted_01_02_03_00
      · exact weighted_01_02_03_01
      · exact weighted_01_02_03_02
      · exact weighted_01_02_03_03
      · exact weighted_01_02_03_04
      · exact weighted_01_02_03_05
      · exact weighted_01_02_03_06
      · exact weighted_01_02_03_07
      · exact weighted_01_02_03_08
      · exact weighted_01_02_03_09
      · exact weighted_01_02_03_10
      · exact weighted_01_02_03_11
      · exact weighted_01_02_03_12
      · exact weighted_01_02_03_13
      · exact weighted_01_02_03_14
      · exact weighted_01_02_03_15
      · exact weighted_01_02_03_16
      · exact weighted_01_02_03_17
      · exact weighted_01_02_03_18
      · exact weighted_01_02_03_19
      · exact weighted_01_02_03_20
      · exact weighted_01_02_03_21
    _ = 2088 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_03

end Paper7MomentGapNumeric
