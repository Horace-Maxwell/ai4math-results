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

theorem row_01_01_00_00 : b4RowContribution (![1, 2, 2, 2] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 2] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 2 = 7
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 13 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 2^2 = 13
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_00

theorem weighted_01_01_00_00 : b4RawGapContribution ![1, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 1 1 0 0 0 row_01_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_00

theorem row_01_01_00_01 : b4RowContribution (![1, 2, 2, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 3] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 3 = 8
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 18 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 3^2 = 18
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_01

theorem weighted_01_01_00_01 : b4RawGapContribution ![1, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 1 1 0 1 0 row_01_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_01

theorem row_01_01_00_02 : b4RowContribution (![1, 2, 2, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 4] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 4 = 9
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 25 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 4^2 = 25
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_02

theorem weighted_01_01_00_02 : b4RawGapContribution ![1, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 1 1 0 2 0 row_01_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_02

def layers_01_01_00_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 14, 17, 18, 17, 14, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_01_00_03

theorem cells_01_01_00_03 : QTableValid (![1, 2, 2, 5] : Fin 4 → ℕ) layers_01_01_00_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_00_03

theorem valid_01_01_00_03 :
    SparseRowValid (![1, 2, 2, 5] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 2, 5] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 2 + 5 = 10
      decide
    have hzsq : (∑ i, (((![1, 2, 2, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 34 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 2^2 + 5^2 = 34
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_00_03
#print axioms Paper7MomentGapNumeric.valid_01_01_00_03

def qvalues_01_01_00_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_00_03

theorem row_01_01_00_03 : b4RowContribution (![1, 2, 2, 5] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 2, 2, 5] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_03) :=
      sparseRow_sound (![1, 2, 2, 5] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_03) valid_01_01_00_03
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_00_03 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_00_03

theorem weighted_01_01_00_03 : b4RawGapContribution ![1, 1, 0, 3] = 12 := by
  calc
    b4RawGapContribution ![1, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 1 :=
      b4GapContribution_from_row 1 1 0 3 1 row_01_01_00_03
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_03

def layers_01_01_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 14, 17, 18, 18, 17, 14, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_01_00_04

theorem cells_01_01_00_04 : QTableValid (![1, 2, 2, 6] : Fin 4 → ℕ) layers_01_01_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_00_04

theorem valid_01_01_00_04 :
    SparseRowValid (![1, 2, 2, 6] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_01_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 2, 6] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 2 + 6 = 11
      decide
    have hzsq : (∑ i, (((![1, 2, 2, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 45 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 2^2 + 6^2 = 45
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_00_04
#print axioms Paper7MomentGapNumeric.valid_01_01_00_04

def qvalues_01_01_00_04 : Fin 19 → ℕ := ![0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_00_04

theorem row_01_01_00_04 : b4RowContribution (![1, 2, 2, 6] : Fin 4 → ℕ) = 14 := by
  calc
    b4RowContribution (![1, 2, 2, 6] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_01_00_04) :=
      sparseRow_sound (![1, 2, 2, 6] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_01_00_04) valid_01_01_00_04
    _ = 14 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_00_04 Q := by
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
        _ = 14 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_00_04

theorem weighted_01_01_00_04 : b4RawGapContribution ![1, 1, 0, 4] = 168 := by
  calc
    b4RawGapContribution ![1, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 14 :=
      b4GapContribution_from_row 1 1 0 4 14 row_01_01_00_04
    _ = 168 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_04

theorem row_01_01_00_05 : b4RowContribution (![1, 2, 2, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 7] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 7 = 12
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 7^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_05

theorem weighted_01_01_00_05 : b4RawGapContribution ![1, 1, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 0 :=
      b4GapContribution_from_row 1 1 0 5 0 row_01_01_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_05

theorem row_01_01_00_06 : b4RowContribution (![1, 2, 2, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 8] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 8 = 13
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 8^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_06

theorem weighted_01_01_00_06 : b4RawGapContribution ![1, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 1 1 0 6 0 row_01_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_06

theorem row_01_01_00_07 : b4RowContribution (![1, 2, 2, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 9] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 9 = 14
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 90 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 9^2 = 90
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_07

theorem weighted_01_01_00_07 : b4RawGapContribution ![1, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 1 1 0 7 0 row_01_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_07

theorem row_01_01_00_08 : b4RowContribution (![1, 2, 2, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 10] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 10 = 15
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 10^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_08

theorem weighted_01_01_00_08 : b4RawGapContribution ![1, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 1 1 0 8 0 row_01_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_08

theorem row_01_01_00_09 : b4RowContribution (![1, 2, 2, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 11] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 11 = 16
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 11^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_09

theorem weighted_01_01_00_09 : b4RawGapContribution ![1, 1, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 0 :=
      b4GapContribution_from_row 1 1 0 9 0 row_01_01_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_09

theorem row_01_01_00_10 : b4RowContribution (![1, 2, 2, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 12] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 12 = 17
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 12^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_10

theorem weighted_01_01_00_10 : b4RawGapContribution ![1, 1, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 0 :=
      b4GapContribution_from_row 1 1 0 10 0 row_01_01_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_10

def layers_01_01_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 14, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 14, 9, 4, 1]]
#print axioms Paper7MomentGapNumeric.layers_01_01_00_11

theorem cells_01_01_00_11 : QTableValid (![1, 2, 2, 13] : Fin 4 → ℕ) layers_01_01_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_00_11

theorem valid_01_01_00_11 :
    SparseRowValid (![1, 2, 2, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 2, 13] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 2 + 13 = 18
      decide
    have hzsq : (∑ i, (((![1, 2, 2, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 2^2 + 13^2 = 178
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_00_11
#print axioms Paper7MomentGapNumeric.valid_01_01_00_11

def qvalues_01_01_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_00_11

theorem row_01_01_00_11 : b4RowContribution (![1, 2, 2, 13] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![1, 2, 2, 13] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_11) :=
      sparseRow_sound (![1, 2, 2, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_00_11) valid_01_01_00_11
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_00_11 Q := by
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
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_00_11

theorem weighted_01_01_00_11 : b4RawGapContribution ![1, 1, 0, 11] = 216 := by
  calc
    b4RawGapContribution ![1, 1, 0, 11] = b4GapPatternWeight 1 0 11 * 18 :=
      b4GapContribution_from_row 1 1 0 11 18 row_01_01_00_11
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_11

theorem row_01_01_00_12 : b4RowContribution (![1, 2, 2, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 14] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 14 = 19
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 14^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_12

theorem weighted_01_01_00_12 : b4RawGapContribution ![1, 1, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 12] = b4GapPatternWeight 1 0 12 * 0 :=
      b4GapContribution_from_row 1 1 0 12 0 row_01_01_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_12

def layers_01_01_00_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 14, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 14, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_01_00_13

theorem cells_01_01_00_13 : QTableValid (![1, 2, 2, 15] : Fin 4 → ℕ) layers_01_01_00_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_00_13

theorem valid_01_01_00_13 :
    SparseRowValid (![1, 2, 2, 15] : Fin 4 → ℕ) ({3, 9, 15} : Finset (Fin 19)) (fun _ => layers_01_01_00_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 2, 15] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 2 + 15 = 20
      decide
    have hzsq : (∑ i, (((![1, 2, 2, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 2^2 + 15^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_00_13
#print axioms Paper7MomentGapNumeric.valid_01_01_00_13

def qvalues_01_01_00_13 : Fin 19 → ℕ := ![0, 0, 0, 14, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 18, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_00_13

theorem row_01_01_00_13 : b4RowContribution (![1, 2, 2, 15] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![1, 2, 2, 15] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9, 15} : Finset (Fin 19)) (fun _ => layers_01_01_00_13) :=
      sparseRow_sound (![1, 2, 2, 15] : Fin 4 → ℕ) ({3, 9, 15} : Finset (Fin 19)) (fun _ => layers_01_01_00_13) valid_01_01_00_13
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_00_13 Q := by
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
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_00_13

theorem weighted_01_01_00_13 : b4RawGapContribution ![1, 1, 0, 13] = 600 := by
  calc
    b4RawGapContribution ![1, 1, 0, 13] = b4GapPatternWeight 1 0 13 * 50 :=
      b4GapContribution_from_row 1 1 0 13 50 row_01_01_00_13
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_13

theorem row_01_01_00_14 : b4RowContribution (![1, 2, 2, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 16] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 16 = 21
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 16^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_14

theorem weighted_01_01_00_14 : b4RawGapContribution ![1, 1, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 14] = b4GapPatternWeight 1 0 14 * 0 :=
      b4GapContribution_from_row 1 1 0 14 0 row_01_01_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_14

theorem row_01_01_00_15 : b4RowContribution (![1, 2, 2, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 17] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 17 = 22
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 17^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_15

theorem weighted_01_01_00_15 : b4RawGapContribution ![1, 1, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 15] = b4GapPatternWeight 1 0 15 * 0 :=
      b4GapContribution_from_row 1 1 0 15 0 row_01_01_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_15

theorem row_01_01_00_16 : b4RowContribution (![1, 2, 2, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 18] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 18 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 18^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_16

theorem weighted_01_01_00_16 : b4RawGapContribution ![1, 1, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 16] = b4GapPatternWeight 1 0 16 * 0 :=
      b4GapContribution_from_row 1 1 0 16 0 row_01_01_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_16

theorem row_01_01_00_17 : b4RowContribution (![1, 2, 2, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 19] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 19 = 24
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 19^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_17

theorem weighted_01_01_00_17 : b4RawGapContribution ![1, 1, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 17] = b4GapPatternWeight 1 0 17 * 0 :=
      b4GapContribution_from_row 1 1 0 17 0 row_01_01_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_17

theorem row_01_01_00_18 : b4RowContribution (![1, 2, 2, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 20] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 20 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 20^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_18

theorem weighted_01_01_00_18 : b4RawGapContribution ![1, 1, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 18] = b4GapPatternWeight 1 0 18 * 0 :=
      b4GapContribution_from_row 1 1 0 18 0 row_01_01_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_18

theorem row_01_01_00_19 : b4RowContribution (![1, 2, 2, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 21] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 21 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 21^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_19

theorem weighted_01_01_00_19 : b4RawGapContribution ![1, 1, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 19] = b4GapPatternWeight 1 0 19 * 0 :=
      b4GapContribution_from_row 1 1 0 19 0 row_01_01_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_19

theorem row_01_01_00_20 : b4RowContribution (![1, 2, 2, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 22] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 22 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 22^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_20

theorem weighted_01_01_00_20 : b4RawGapContribution ![1, 1, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 20] = b4GapPatternWeight 1 0 20 * 0 :=
      b4GapContribution_from_row 1 1 0 20 0 row_01_01_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_20

theorem row_01_01_00_21 : b4RowContribution (![1, 2, 2, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 23] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 23 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 538 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 23^2 = 538
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_21

theorem weighted_01_01_00_21 : b4RawGapContribution ![1, 1, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 21] = b4GapPatternWeight 1 0 21 * 0 :=
      b4GapContribution_from_row 1 1 0 21 0 row_01_01_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_21

theorem row_01_01_00_22 : b4RowContribution (![1, 2, 2, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 24] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 24 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 24^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_22

theorem weighted_01_01_00_22 : b4RawGapContribution ![1, 1, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 22] = b4GapPatternWeight 1 0 22 * 0 :=
      b4GapContribution_from_row 1 1 0 22 0 row_01_01_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_22

theorem row_01_01_00_23 : b4RowContribution (![1, 2, 2, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 25] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 25 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 634 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 25^2 = 634
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_23

theorem weighted_01_01_00_23 : b4RawGapContribution ![1, 1, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 23] = b4GapPatternWeight 1 0 23 * 0 :=
      b4GapContribution_from_row 1 1 0 23 0 row_01_01_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_23

theorem row_01_01_00_24 : b4RowContribution (![1, 2, 2, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 26] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 26 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 685 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 26^2 = 685
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_24

theorem weighted_01_01_00_24 : b4RawGapContribution ![1, 1, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 24] = b4GapPatternWeight 1 0 24 * 0 :=
      b4GapContribution_from_row 1 1 0 24 0 row_01_01_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_24

theorem row_01_01_00_25 : b4RowContribution (![1, 2, 2, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 27] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 27 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 738 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 27^2 = 738
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_25

theorem weighted_01_01_00_25 : b4RawGapContribution ![1, 1, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 25] = b4GapPatternWeight 1 0 25 * 0 :=
      b4GapContribution_from_row 1 1 0 25 0 row_01_01_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_25

theorem row_01_01_00_26 : b4RowContribution (![1, 2, 2, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 28] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 28 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 793 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 28^2 = 793
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_26

theorem weighted_01_01_00_26 : b4RawGapContribution ![1, 1, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 26] = b4GapPatternWeight 1 0 26 * 0 :=
      b4GapContribution_from_row 1 1 0 26 0 row_01_01_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_26

theorem row_01_01_00_27 : b4RowContribution (![1, 2, 2, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 29] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 29 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 850 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 29^2 = 850
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_27

theorem weighted_01_01_00_27 : b4RawGapContribution ![1, 1, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 27] = b4GapPatternWeight 1 0 27 * 0 :=
      b4GapContribution_from_row 1 1 0 27 0 row_01_01_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_27

theorem row_01_01_00_28 : b4RowContribution (![1, 2, 2, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 30] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 30 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 909 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 30^2 = 909
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_28

theorem weighted_01_01_00_28 : b4RawGapContribution ![1, 1, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 28] = b4GapPatternWeight 1 0 28 * 0 :=
      b4GapContribution_from_row 1 1 0 28 0 row_01_01_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_28

theorem row_01_01_00_29 : b4RowContribution (![1, 2, 2, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 31] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 31 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 970 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 31^2 = 970
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_29

theorem weighted_01_01_00_29 : b4RawGapContribution ![1, 1, 0, 29] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 29] = b4GapPatternWeight 1 0 29 * 0 :=
      b4GapContribution_from_row 1 1 0 29 0 row_01_01_00_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_29

theorem row_01_01_00_30 : b4RowContribution (![1, 2, 2, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 2, 32] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 2 + 32 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 2, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1033 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 2^2 + 32^2 = 1033
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_00_30

theorem weighted_01_01_00_30 : b4RawGapContribution ![1, 1, 0, 30] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 0, 30] = b4GapPatternWeight 1 0 30 * 0 :=
      b4GapContribution_from_row 1 1 0 30 0 row_01_01_00_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_00_30

def dvalues_01_01_00 : Fin 31 → ℕ := ![0, 0, 0, 12, 168, 0, 0, 0, 0, 0, 0, 216, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_00

theorem dblock_01_01_00 : b4GapPatternDBlock 1 1 0 = 996 := by
  calc
    b4GapPatternDBlock 1 1 0 = ∑ d : Fin 31, dvalues_01_01_00 d := by
      apply b4GapDBlock_of_rows 1 1 0 dvalues_01_01_00
      intro d
      fin_cases d
      · exact weighted_01_01_00_00
      · exact weighted_01_01_00_01
      · exact weighted_01_01_00_02
      · exact weighted_01_01_00_03
      · exact weighted_01_01_00_04
      · exact weighted_01_01_00_05
      · exact weighted_01_01_00_06
      · exact weighted_01_01_00_07
      · exact weighted_01_01_00_08
      · exact weighted_01_01_00_09
      · exact weighted_01_01_00_10
      · exact weighted_01_01_00_11
      · exact weighted_01_01_00_12
      · exact weighted_01_01_00_13
      · exact weighted_01_01_00_14
      · exact weighted_01_01_00_15
      · exact weighted_01_01_00_16
      · exact weighted_01_01_00_17
      · exact weighted_01_01_00_18
      · exact weighted_01_01_00_19
      · exact weighted_01_01_00_20
      · exact weighted_01_01_00_21
      · exact weighted_01_01_00_22
      · exact weighted_01_01_00_23
      · exact weighted_01_01_00_24
      · exact weighted_01_01_00_25
      · exact weighted_01_01_00_26
      · exact weighted_01_01_00_27
      · exact weighted_01_01_00_28
      · exact weighted_01_01_00_29
      · exact weighted_01_01_00_30
    _ = 996 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_00

end Paper7MomentGapNumeric
