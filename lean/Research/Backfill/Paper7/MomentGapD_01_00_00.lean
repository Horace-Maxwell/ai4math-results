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

theorem row_01_00_00_00 : b4RowContribution (![1, 1, 1, 1] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 1] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 1 = 4
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 4 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 1^2 = 4
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_00

theorem weighted_01_00_00_00 : b4RawGapContribution ![1, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 1 0 0 0 0 row_01_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_00

theorem row_01_00_00_01 : b4RowContribution (![1, 1, 1, 2] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 2] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 2 = 5
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 7 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 2^2 = 7
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_01

theorem weighted_01_00_00_01 : b4RawGapContribution ![1, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 1 0 0 1 0 row_01_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_01

theorem row_01_00_00_02 : b4RowContribution (![1, 1, 1, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 3] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 3 = 6
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 12 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 3^2 = 12
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_02

theorem weighted_01_00_00_02 : b4RawGapContribution ![1, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 1 0 0 2 0 row_01_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_02

theorem row_01_00_00_03 : b4RowContribution (![1, 1, 1, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 4] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 4 = 7
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 19 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 4^2 = 19
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_03

theorem weighted_01_00_00_03 : b4RawGapContribution ![1, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 1 0 0 3 0 row_01_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_03

theorem row_01_00_00_04 : b4RowContribution (![1, 1, 1, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 5] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 5 = 8
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 28 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 5^2 = 28
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_04

theorem weighted_01_00_00_04 : b4RawGapContribution ![1, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 1 0 0 4 0 row_01_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_04

def layers_01_00_00_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 7, 8, 8, 8, 8, 7, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_00_05

theorem cells_01_00_00_05 : QTableValid (![1, 1, 1, 6] : Fin 4 → ℕ) layers_01_00_00_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_00_05

theorem valid_01_00_00_05 :
    SparseRowValid (![1, 1, 1, 6] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_00_00_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 1, 6] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 1 + 6 = 9
      decide
    have hzsq : (∑ i, (((![1, 1, 1, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 39 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 1^2 + 6^2 = 39
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_00_05
#print axioms Paper7MomentGapNumeric.valid_01_00_00_05

def qvalues_01_00_00_05 : Fin 19 → ℕ := ![0, 0, 0, 8, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_00_05

theorem row_01_00_00_05 : b4RowContribution (![1, 1, 1, 6] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![1, 1, 1, 6] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_00_00_05) :=
      sparseRow_sound (![1, 1, 1, 6] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_00_00_05) valid_01_00_00_05
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_00_05 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_00_05

theorem weighted_01_00_00_05 : b4RawGapContribution ![1, 0, 0, 5] = 36 := by
  calc
    b4RawGapContribution ![1, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 9 :=
      b4GapContribution_from_row 1 0 0 5 9 row_01_00_00_05
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_05

theorem row_01_00_00_06 : b4RowContribution (![1, 1, 1, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 7] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 7 = 10
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 52 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 7^2 = 52
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_06

theorem weighted_01_00_00_06 : b4RawGapContribution ![1, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 1 0 0 6 0 row_01_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_06

theorem row_01_00_00_07 : b4RowContribution (![1, 1, 1, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 8] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 8 = 11
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 67 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 8^2 = 67
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_07

theorem weighted_01_00_00_07 : b4RawGapContribution ![1, 0, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 0 :=
      b4GapContribution_from_row 1 0 0 7 0 row_01_00_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_07

theorem row_01_00_00_08 : b4RowContribution (![1, 1, 1, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 9] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 9 = 12
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 84 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 9^2 = 84
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_08

theorem weighted_01_00_00_08 : b4RawGapContribution ![1, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 1 0 0 8 0 row_01_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_08

theorem row_01_00_00_09 : b4RowContribution (![1, 1, 1, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 10] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 10 = 13
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 103 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 10^2 = 103
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_09

theorem weighted_01_00_00_09 : b4RawGapContribution ![1, 0, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 0 :=
      b4GapContribution_from_row 1 0 0 9 0 row_01_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_09

theorem row_01_00_00_10 : b4RowContribution (![1, 1, 1, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 11] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 11 = 14
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 11^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_10

theorem weighted_01_00_00_10 : b4RawGapContribution ![1, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 1 0 0 10 0 row_01_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_10

theorem row_01_00_00_11 : b4RowContribution (![1, 1, 1, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 12] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 12 = 15
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 147 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 12^2 = 147
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_11

theorem weighted_01_00_00_11 : b4RawGapContribution ![1, 0, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 0 :=
      b4GapContribution_from_row 1 0 0 11 0 row_01_00_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_11

def layers_01_00_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 4, 1, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_00_12

theorem cells_01_00_00_12 : QTableValid (![1, 1, 1, 13] : Fin 4 → ℕ) layers_01_00_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_00_12

theorem valid_01_00_00_12 :
    SparseRowValid (![1, 1, 1, 13] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 1, 13] : Fin 4 → ℕ) i) = 16 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 1 + 13 = 16
      decide
    have hzsq : (∑ i, (((![1, 1, 1, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 1^2 + 13^2 = 172
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_00_12
#print axioms Paper7MomentGapNumeric.valid_01_00_00_12

def qvalues_01_00_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 1, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_00_12

theorem row_01_00_00_12 : b4RowContribution (![1, 1, 1, 13] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![1, 1, 1, 13] : Fin 4 → ℕ) =
        sparseRowValue ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_12) :=
      sparseRow_sound (![1, 1, 1, 13] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_12) valid_01_00_00_12
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_00_12 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_00_12

theorem weighted_01_00_00_12 : b4RawGapContribution ![1, 0, 0, 12] = 36 := by
  calc
    b4RawGapContribution ![1, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 9 :=
      b4GapContribution_from_row 1 0 0 12 9 row_01_00_00_12
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_12

theorem row_01_00_00_13 : b4RowContribution (![1, 1, 1, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 14] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 14 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 199 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 14^2 = 199
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_13

theorem weighted_01_00_00_13 : b4RawGapContribution ![1, 0, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 0 :=
      b4GapContribution_from_row 1 0 0 13 0 row_01_00_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_13

def layers_01_00_00_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 4, 1]]
#print axioms Paper7MomentGapNumeric.layers_01_00_00_14

theorem cells_01_00_00_14 : QTableValid (![1, 1, 1, 15] : Fin 4 → ℕ) layers_01_00_00_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_00_14

theorem valid_01_00_00_14 :
    SparseRowValid (![1, 1, 1, 15] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_01_00_00_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 1, 15] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 1 + 15 = 18
      decide
    have hzsq : (∑ i, (((![1, 1, 1, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 1^2 + 15^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_00_14
#print axioms Paper7MomentGapNumeric.valid_01_00_00_14

def qvalues_01_00_00_14 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_00_14

theorem row_01_00_00_14 : b4RowContribution (![1, 1, 1, 15] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 1, 1, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9, 15} : Finset (Fin 19)) (fun _ => layers_01_00_00_14) :=
      sparseRow_sound (![1, 1, 1, 15] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_01_00_00_14) valid_01_00_00_14
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_00_14 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_00_14

theorem weighted_01_00_00_14 : b4RawGapContribution ![1, 0, 0, 14] = 64 := by
  calc
    b4RawGapContribution ![1, 0, 0, 14] = b4GapPatternWeight 0 0 14 * 16 :=
      b4GapContribution_from_row 1 0 0 14 16 row_01_00_00_14
    _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_14

theorem row_01_00_00_15 : b4RowContribution (![1, 1, 1, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 16] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 16 = 19
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 16^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_15

theorem weighted_01_00_00_15 : b4RawGapContribution ![1, 0, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 15] = b4GapPatternWeight 0 0 15 * 0 :=
      b4GapContribution_from_row 1 0 0 15 0 row_01_00_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_15

def layers_01_00_00_16 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7]]
#print axioms Paper7MomentGapNumeric.layers_01_00_00_16

theorem cells_01_00_00_16 : QTableValid (![1, 1, 1, 17] : Fin 4 → ℕ) layers_01_00_00_16 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_00_16

theorem valid_01_00_00_16 :
    SparseRowValid (![1, 1, 1, 17] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_16) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 1, 17] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 1 + 17 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 1, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 1^2 + 17^2 = 292
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_00_16
#print axioms Paper7MomentGapNumeric.valid_01_00_00_16

def qvalues_01_00_00_16 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_00_16

theorem row_01_00_00_16 : b4RowContribution (![1, 1, 1, 17] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 1, 1, 17] : Fin 4 → ℕ) =
        sparseRowValue ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_16) :=
      sparseRow_sound (![1, 1, 1, 17] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_00_00_16) valid_01_00_00_16
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_00_16 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_00_16

theorem weighted_01_00_00_16 : b4RawGapContribution ![1, 0, 0, 16] = 64 := by
  calc
    b4RawGapContribution ![1, 0, 0, 16] = b4GapPatternWeight 0 0 16 * 16 :=
      b4GapContribution_from_row 1 0 0 16 16 row_01_00_00_16
    _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_16

theorem row_01_00_00_17 : b4RowContribution (![1, 1, 1, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 18] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 18 = 21
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 18^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_17

theorem weighted_01_00_00_17 : b4RawGapContribution ![1, 0, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 17] = b4GapPatternWeight 0 0 17 * 0 :=
      b4GapContribution_from_row 1 0 0 17 0 row_01_00_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_17

theorem row_01_00_00_18 : b4RowContribution (![1, 1, 1, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 19] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 19 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 19^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_18

theorem weighted_01_00_00_18 : b4RawGapContribution ![1, 0, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 18] = b4GapPatternWeight 0 0 18 * 0 :=
      b4GapContribution_from_row 1 0 0 18 0 row_01_00_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_18

theorem row_01_00_00_19 : b4RowContribution (![1, 1, 1, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 20] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 20 = 23
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 20^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_19

theorem weighted_01_00_00_19 : b4RawGapContribution ![1, 0, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 19] = b4GapPatternWeight 0 0 19 * 0 :=
      b4GapContribution_from_row 1 0 0 19 0 row_01_00_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_19

theorem row_01_00_00_20 : b4RowContribution (![1, 1, 1, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 21] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 21 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 21^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_20

theorem weighted_01_00_00_20 : b4RawGapContribution ![1, 0, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 20] = b4GapPatternWeight 0 0 20 * 0 :=
      b4GapContribution_from_row 1 0 0 20 0 row_01_00_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_20

theorem row_01_00_00_21 : b4RowContribution (![1, 1, 1, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 22] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 22 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 22^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_21

theorem weighted_01_00_00_21 : b4RawGapContribution ![1, 0, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 21] = b4GapPatternWeight 0 0 21 * 0 :=
      b4GapContribution_from_row 1 0 0 21 0 row_01_00_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_21

theorem row_01_00_00_22 : b4RowContribution (![1, 1, 1, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 23] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 23 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 532 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 23^2 = 532
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_22

theorem weighted_01_00_00_22 : b4RawGapContribution ![1, 0, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 22] = b4GapPatternWeight 0 0 22 * 0 :=
      b4GapContribution_from_row 1 0 0 22 0 row_01_00_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_22

theorem row_01_00_00_23 : b4RowContribution (![1, 1, 1, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 24] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 24 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 24^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_23

theorem weighted_01_00_00_23 : b4RawGapContribution ![1, 0, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 23] = b4GapPatternWeight 0 0 23 * 0 :=
      b4GapContribution_from_row 1 0 0 23 0 row_01_00_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_23

theorem row_01_00_00_24 : b4RowContribution (![1, 1, 1, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 25] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 25 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 628 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 25^2 = 628
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_24

theorem weighted_01_00_00_24 : b4RawGapContribution ![1, 0, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 24] = b4GapPatternWeight 0 0 24 * 0 :=
      b4GapContribution_from_row 1 0 0 24 0 row_01_00_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_24

theorem row_01_00_00_25 : b4RowContribution (![1, 1, 1, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 26] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 26 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 679 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 26^2 = 679
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_25

theorem weighted_01_00_00_25 : b4RawGapContribution ![1, 0, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 25] = b4GapPatternWeight 0 0 25 * 0 :=
      b4GapContribution_from_row 1 0 0 25 0 row_01_00_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_25

theorem row_01_00_00_26 : b4RowContribution (![1, 1, 1, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 27] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 27 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 732 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 27^2 = 732
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_26

theorem weighted_01_00_00_26 : b4RawGapContribution ![1, 0, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 26] = b4GapPatternWeight 0 0 26 * 0 :=
      b4GapContribution_from_row 1 0 0 26 0 row_01_00_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_26

theorem row_01_00_00_27 : b4RowContribution (![1, 1, 1, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 28] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 28 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 787 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 28^2 = 787
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_27

theorem weighted_01_00_00_27 : b4RawGapContribution ![1, 0, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 27] = b4GapPatternWeight 0 0 27 * 0 :=
      b4GapContribution_from_row 1 0 0 27 0 row_01_00_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_27

theorem row_01_00_00_28 : b4RowContribution (![1, 1, 1, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 29] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 29 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 844 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 29^2 = 844
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_28

theorem weighted_01_00_00_28 : b4RawGapContribution ![1, 0, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 28] = b4GapPatternWeight 0 0 28 * 0 :=
      b4GapContribution_from_row 1 0 0 28 0 row_01_00_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_28

theorem row_01_00_00_29 : b4RowContribution (![1, 1, 1, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 30] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 30 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 903 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 30^2 = 903
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_29

theorem weighted_01_00_00_29 : b4RawGapContribution ![1, 0, 0, 29] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 29] = b4GapPatternWeight 0 0 29 * 0 :=
      b4GapContribution_from_row 1 0 0 29 0 row_01_00_00_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_29

theorem row_01_00_00_30 : b4RowContribution (![1, 1, 1, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 31] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 31 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 964 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 31^2 = 964
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_30

theorem weighted_01_00_00_30 : b4RawGapContribution ![1, 0, 0, 30] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 30] = b4GapPatternWeight 0 0 30 * 0 :=
      b4GapContribution_from_row 1 0 0 30 0 row_01_00_00_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_30

theorem row_01_00_00_31 : b4RowContribution (![1, 1, 1, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 32] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 32 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1027 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 32^2 = 1027
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_31

theorem weighted_01_00_00_31 : b4RawGapContribution ![1, 0, 0, 31] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 31] = b4GapPatternWeight 0 0 31 * 0 :=
      b4GapContribution_from_row 1 0 0 31 0 row_01_00_00_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_31

theorem row_01_00_00_32 : b4RowContribution (![1, 1, 1, 33] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 33] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 33 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1092 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 33^2 = 1092
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_32

theorem weighted_01_00_00_32 : b4RawGapContribution ![1, 0, 0, 32] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 32] = b4GapPatternWeight 0 0 32 * 0 :=
      b4GapContribution_from_row 1 0 0 32 0 row_01_00_00_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_32

theorem row_01_00_00_33 : b4RowContribution (![1, 1, 1, 34] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 1, 34] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 1 + 34 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 1, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1159 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 1^2 + 34^2 = 1159
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_00_33

theorem weighted_01_00_00_33 : b4RawGapContribution ![1, 0, 0, 33] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 0, 33] = b4GapPatternWeight 0 0 33 * 0 :=
      b4GapContribution_from_row 1 0 0 33 0 row_01_00_00_33
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_00_33

def dvalues_01_00_00 : Fin 34 → ℕ := ![0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 36, 0, 64, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_00

theorem dblock_01_00_00 : b4GapPatternDBlock 1 0 0 = 200 := by
  calc
    b4GapPatternDBlock 1 0 0 = ∑ d : Fin 34, dvalues_01_00_00 d := by
      apply b4GapDBlock_of_rows 1 0 0 dvalues_01_00_00
      intro d
      fin_cases d
      · exact weighted_01_00_00_00
      · exact weighted_01_00_00_01
      · exact weighted_01_00_00_02
      · exact weighted_01_00_00_03
      · exact weighted_01_00_00_04
      · exact weighted_01_00_00_05
      · exact weighted_01_00_00_06
      · exact weighted_01_00_00_07
      · exact weighted_01_00_00_08
      · exact weighted_01_00_00_09
      · exact weighted_01_00_00_10
      · exact weighted_01_00_00_11
      · exact weighted_01_00_00_12
      · exact weighted_01_00_00_13
      · exact weighted_01_00_00_14
      · exact weighted_01_00_00_15
      · exact weighted_01_00_00_16
      · exact weighted_01_00_00_17
      · exact weighted_01_00_00_18
      · exact weighted_01_00_00_19
      · exact weighted_01_00_00_20
      · exact weighted_01_00_00_21
      · exact weighted_01_00_00_22
      · exact weighted_01_00_00_23
      · exact weighted_01_00_00_24
      · exact weighted_01_00_00_25
      · exact weighted_01_00_00_26
      · exact weighted_01_00_00_27
      · exact weighted_01_00_00_28
      · exact weighted_01_00_00_29
      · exact weighted_01_00_00_30
      · exact weighted_01_00_00_31
      · exact weighted_01_00_00_32
      · exact weighted_01_00_00_33
    _ = 200 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_00

end Paper7MomentGapNumeric
