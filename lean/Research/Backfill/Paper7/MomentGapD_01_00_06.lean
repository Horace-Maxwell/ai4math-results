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

theorem row_01_00_06_00 : b4RowContribution (![1, 1, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 7 = 16
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 7^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_00

theorem weighted_01_00_06_00 : b4RawGapContribution ![1, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 1 0 6 0 0 row_01_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_00

theorem row_01_00_06_01 : b4RowContribution (![1, 1, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 8 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 115 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 8^2 = 115
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_01

theorem weighted_01_00_06_01 : b4RawGapContribution ![1, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 1 0 6 1 0 row_01_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_01

theorem row_01_00_06_02 : b4RowContribution (![1, 1, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 9 = 18
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 9^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_02

theorem weighted_01_00_06_02 : b4RawGapContribution ![1, 0, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 0 :=
      b4GapContribution_from_row 1 0 6 2 0 row_01_00_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_02

theorem row_01_00_06_03 : b4RowContribution (![1, 1, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 10 = 19
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 151 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 10^2 = 151
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_03

theorem weighted_01_00_06_03 : b4RawGapContribution ![1, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 1 0 6 3 0 row_01_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_03

def layers_01_00_06_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 31, 32, 32, 32, 31, 28, 24, 20, 16, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_06_04

theorem cells_01_00_06_04 : QTableValid (![1, 1, 7, 11] : Fin 4 → ℕ) layers_01_00_06_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_06_04

theorem valid_01_00_06_04 :
    SparseRowValid (![1, 1, 7, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_06_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 7, 11] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 7 + 11 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 7^2 + 11^2 = 172
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_06_04
#print axioms Paper7MomentGapNumeric.valid_01_00_06_04

def qvalues_01_00_06_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_06_04

theorem row_01_00_06_04 : b4RowContribution (![1, 1, 7, 11] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 1, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_00_06_04) :=
      sparseRow_sound (![1, 1, 7, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_06_04) valid_01_00_06_04
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_06_04 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_06_04

theorem weighted_01_00_06_04 : b4RawGapContribution ![1, 0, 6, 4] = 384 := by
  calc
    b4RawGapContribution ![1, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 32 :=
      b4GapContribution_from_row 1 0 6 4 32 row_01_00_06_04
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_04

theorem row_01_00_06_05 : b4RowContribution (![1, 1, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 12 = 21
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 12^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_05

theorem weighted_01_00_06_05 : b4RawGapContribution ![1, 0, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 0 :=
      b4GapContribution_from_row 1 0 6 5 0 row_01_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_05

def layers_01_00_06_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 31, 32, 32, 32, 32, 32, 31, 28, 24, 20, 16]]
#print axioms Paper7MomentGapNumeric.layers_01_00_06_06

theorem cells_01_00_06_06 : QTableValid (![1, 1, 7, 13] : Fin 4 → ℕ) layers_01_00_06_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_06_06

theorem valid_01_00_06_06 :
    SparseRowValid (![1, 1, 7, 13] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_06_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 7, 13] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 7 + 13 = 22
      decide
    have hzsq : (∑ i, (((![1, 1, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 7^2 + 13^2 = 220
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_06_06
#print axioms Paper7MomentGapNumeric.valid_01_00_06_06

def qvalues_01_00_06_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_06_06

theorem row_01_00_06_06 : b4RowContribution (![1, 1, 7, 13] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 1, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_01_00_06_06) :=
      sparseRow_sound (![1, 1, 7, 13] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_06_06) valid_01_00_06_06
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_06_06 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_06_06

theorem weighted_01_00_06_06 : b4RawGapContribution ![1, 0, 6, 6] = 384 := by
  calc
    b4RawGapContribution ![1, 0, 6, 6] = b4GapPatternWeight 0 6 6 * 32 :=
      b4GapContribution_from_row 1 0 6 6 32 row_01_00_06_06
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_06

theorem row_01_00_06_07 : b4RowContribution (![1, 1, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 14] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 14 = 23
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 14^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_07

theorem weighted_01_00_06_07 : b4RawGapContribution ![1, 0, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 7] = b4GapPatternWeight 0 6 7 * 0 :=
      b4GapContribution_from_row 1 0 6 7 0 row_01_00_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_07

def layers_01_00_06_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 31, 32, 32, 32, 32, 32, 32, 32, 31, 28, 24]]
#print axioms Paper7MomentGapNumeric.layers_01_00_06_08

theorem cells_01_00_06_08 : QTableValid (![1, 1, 7, 15] : Fin 4 → ℕ) layers_01_00_06_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_06_08

theorem valid_01_00_06_08 :
    SparseRowValid (![1, 1, 7, 15] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_00_06_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 7, 15] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 7 + 15 = 24
      decide
    have hzsq : (∑ i, (((![1, 1, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 7^2 + 15^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_06_08
#print axioms Paper7MomentGapNumeric.valid_01_00_06_08

def qvalues_01_00_06_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_06_08

theorem row_01_00_06_08 : b4RowContribution (![1, 1, 7, 15] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 1, 7, 15] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_01_00_06_08) :=
      sparseRow_sound (![1, 1, 7, 15] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_00_06_08) valid_01_00_06_08
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_06_08 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_06_08

theorem weighted_01_00_06_08 : b4RawGapContribution ![1, 0, 6, 8] = 384 := by
  calc
    b4RawGapContribution ![1, 0, 6, 8] = b4GapPatternWeight 0 6 8 * 32 :=
      b4GapContribution_from_row 1 0 6 8 32 row_01_00_06_08
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_08

theorem row_01_00_06_09 : b4RowContribution (![1, 1, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 16] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 16 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 16^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_09

theorem weighted_01_00_06_09 : b4RawGapContribution ![1, 0, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 9] = b4GapPatternWeight 0 6 9 * 0 :=
      b4GapContribution_from_row 1 0 6 9 0 row_01_00_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_09

theorem row_01_00_06_10 : b4RowContribution (![1, 1, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 17 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 17^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_10

theorem weighted_01_00_06_10 : b4RawGapContribution ![1, 0, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 10] = b4GapPatternWeight 0 6 10 * 0 :=
      b4GapContribution_from_row 1 0 6 10 0 row_01_00_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_10

theorem row_01_00_06_11 : b4RowContribution (![1, 1, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 18 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 18^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_11

theorem weighted_01_00_06_11 : b4RawGapContribution ![1, 0, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 11] = b4GapPatternWeight 0 6 11 * 0 :=
      b4GapContribution_from_row 1 0 6 11 0 row_01_00_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_11

theorem row_01_00_06_12 : b4RowContribution (![1, 1, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 19 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 412 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 19^2 = 412
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_12

theorem weighted_01_00_06_12 : b4RawGapContribution ![1, 0, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 12] = b4GapPatternWeight 0 6 12 * 0 :=
      b4GapContribution_from_row 1 0 6 12 0 row_01_00_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_12

theorem row_01_00_06_13 : b4RowContribution (![1, 1, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 20 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 20^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_13

theorem weighted_01_00_06_13 : b4RawGapContribution ![1, 0, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 13] = b4GapPatternWeight 0 6 13 * 0 :=
      b4GapContribution_from_row 1 0 6 13 0 row_01_00_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_13

theorem row_01_00_06_14 : b4RowContribution (![1, 1, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 21 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 492 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 21^2 = 492
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_14

theorem weighted_01_00_06_14 : b4RawGapContribution ![1, 0, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 14] = b4GapPatternWeight 0 6 14 * 0 :=
      b4GapContribution_from_row 1 0 6 14 0 row_01_00_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_14

theorem row_01_00_06_15 : b4RowContribution (![1, 1, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 22 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 535 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 22^2 = 535
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_15

theorem weighted_01_00_06_15 : b4RawGapContribution ![1, 0, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 15] = b4GapPatternWeight 0 6 15 * 0 :=
      b4GapContribution_from_row 1 0 6 15 0 row_01_00_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_15

theorem row_01_00_06_16 : b4RowContribution (![1, 1, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 23 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 580 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 23^2 = 580
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_16

theorem weighted_01_00_06_16 : b4RawGapContribution ![1, 0, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 16] = b4GapPatternWeight 0 6 16 * 0 :=
      b4GapContribution_from_row 1 0 6 16 0 row_01_00_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_16

theorem row_01_00_06_17 : b4RowContribution (![1, 1, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 24 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 627 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 24^2 = 627
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_17

theorem weighted_01_00_06_17 : b4RawGapContribution ![1, 0, 6, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 17] = b4GapPatternWeight 0 6 17 * 0 :=
      b4GapContribution_from_row 1 0 6 17 0 row_01_00_06_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_17

theorem row_01_00_06_18 : b4RowContribution (![1, 1, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 25 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 676 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 25^2 = 676
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_18

theorem weighted_01_00_06_18 : b4RawGapContribution ![1, 0, 6, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 18] = b4GapPatternWeight 0 6 18 * 0 :=
      b4GapContribution_from_row 1 0 6 18 0 row_01_00_06_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_18

theorem row_01_00_06_19 : b4RowContribution (![1, 1, 7, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 26 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 727 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 26^2 = 727
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_19

theorem weighted_01_00_06_19 : b4RawGapContribution ![1, 0, 6, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 19] = b4GapPatternWeight 0 6 19 * 0 :=
      b4GapContribution_from_row 1 0 6 19 0 row_01_00_06_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_19

theorem row_01_00_06_20 : b4RowContribution (![1, 1, 7, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 27 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 780 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 27^2 = 780
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_20

theorem weighted_01_00_06_20 : b4RawGapContribution ![1, 0, 6, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 20] = b4GapPatternWeight 0 6 20 * 0 :=
      b4GapContribution_from_row 1 0 6 20 0 row_01_00_06_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_20

theorem row_01_00_06_21 : b4RowContribution (![1, 1, 7, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 7, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 7 + 28 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 7, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 835 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 7^2 + 28^2 = 835
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_06_21

theorem weighted_01_00_06_21 : b4RawGapContribution ![1, 0, 6, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 6, 21] = b4GapPatternWeight 0 6 21 * 0 :=
      b4GapContribution_from_row 1 0 6 21 0 row_01_00_06_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_06_21

def dvalues_01_00_06 : Fin 22 → ℕ := ![0, 0, 0, 0, 384, 0, 384, 0, 384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_06

theorem dblock_01_00_06 : b4GapPatternDBlock 1 0 6 = 1152 := by
  calc
    b4GapPatternDBlock 1 0 6 = ∑ d : Fin 22, dvalues_01_00_06 d := by
      apply b4GapDBlock_of_rows 1 0 6 dvalues_01_00_06
      intro d
      fin_cases d
      · exact weighted_01_00_06_00
      · exact weighted_01_00_06_01
      · exact weighted_01_00_06_02
      · exact weighted_01_00_06_03
      · exact weighted_01_00_06_04
      · exact weighted_01_00_06_05
      · exact weighted_01_00_06_06
      · exact weighted_01_00_06_07
      · exact weighted_01_00_06_08
      · exact weighted_01_00_06_09
      · exact weighted_01_00_06_10
      · exact weighted_01_00_06_11
      · exact weighted_01_00_06_12
      · exact weighted_01_00_06_13
      · exact weighted_01_00_06_14
      · exact weighted_01_00_06_15
      · exact weighted_01_00_06_16
      · exact weighted_01_00_06_17
      · exact weighted_01_00_06_18
      · exact weighted_01_00_06_19
      · exact weighted_01_00_06_20
      · exact weighted_01_00_06_21
    _ = 1152 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_06

end Paper7MomentGapNumeric
