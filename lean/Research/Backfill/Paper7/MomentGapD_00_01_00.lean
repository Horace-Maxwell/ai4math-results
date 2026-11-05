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

theorem row_00_01_00_00 : b4RowContribution (![0, 1, 1, 1] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 1] : Fin 4 → ℕ) i) = 3 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 1 = 3
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 3 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 1^2 = 3
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_00

theorem weighted_00_01_00_00 : b4RawGapContribution ![0, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 0 1 0 0 0 row_00_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_00

theorem row_00_01_00_01 : b4RowContribution (![0, 1, 1, 2] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 2] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 2 = 4
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 6 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 2^2 = 6
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_01

theorem weighted_00_01_00_01 : b4RawGapContribution ![0, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 0 1 0 1 0 row_00_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_01

theorem row_00_01_00_02 : b4RowContribution (![0, 1, 1, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 3] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 3 = 5
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 11 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 3^2 = 11
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_02

theorem weighted_00_01_00_02 : b4RawGapContribution ![0, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 0 1 0 2 0 row_00_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_02

theorem row_00_01_00_03 : b4RowContribution (![0, 1, 1, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 4] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 4 = 6
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 18 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 4^2 = 18
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_03

theorem weighted_00_01_00_03 : b4RawGapContribution ![0, 1, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 0 :=
      b4GapContribution_from_row 0 1 0 3 0 row_00_01_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_03

theorem row_00_01_00_04 : b4RowContribution (![0, 1, 1, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 5] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 5 = 7
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 27 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 5^2 = 27
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_04

theorem weighted_00_01_00_04 : b4RawGapContribution ![0, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 0 1 0 4 0 row_00_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_04

def layers_00_01_00_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_00_05

theorem cells_00_01_00_05 : QTableValid (![0, 1, 1, 6] : Fin 4 → ℕ) layers_00_01_00_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_00_05

theorem valid_00_01_00_05 :
    SparseRowValid (![0, 1, 1, 6] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_00_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 1, 6] : Fin 4 → ℕ) i) = 8 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 1 + 6 = 8
      decide
    have hzsq : (∑ i, (((![0, 1, 1, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 38 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 1^2 + 6^2 = 38
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_00_05
#print axioms Paper7MomentGapNumeric.valid_00_01_00_05

def qvalues_00_01_00_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_00_05

theorem row_00_01_00_05 : b4RowContribution (![0, 1, 1, 6] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![0, 1, 1, 6] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_01_00_05) :=
      sparseRow_sound (![0, 1, 1, 6] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_01_00_05) valid_00_01_00_05
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_00_05 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_00_05

theorem weighted_00_01_00_05 : b4RawGapContribution ![0, 1, 0, 5] = 48 := by
  calc
    b4RawGapContribution ![0, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 4 :=
      b4GapContribution_from_row 0 1 0 5 4 row_00_01_00_05
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_05

theorem row_00_01_00_06 : b4RowContribution (![0, 1, 1, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 7] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 7 = 9
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 51 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 7^2 = 51
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_06

theorem weighted_00_01_00_06 : b4RawGapContribution ![0, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 0 1 0 6 0 row_00_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_06

theorem row_00_01_00_07 : b4RowContribution (![0, 1, 1, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 8] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 8 = 10
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 66 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 8^2 = 66
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_07

theorem weighted_00_01_00_07 : b4RawGapContribution ![0, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 0 1 0 7 0 row_00_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_07

theorem row_00_01_00_08 : b4RowContribution (![0, 1, 1, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 9] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 9 = 11
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 83 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 9^2 = 83
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_08

theorem weighted_00_01_00_08 : b4RawGapContribution ![0, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 0 1 0 8 0 row_00_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_08

theorem row_00_01_00_09 : b4RowContribution (![0, 1, 1, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 10] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 10 = 12
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 102 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 10^2 = 102
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_09

theorem weighted_00_01_00_09 : b4RawGapContribution ![0, 1, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 0 :=
      b4GapContribution_from_row 0 1 0 9 0 row_00_01_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_09

theorem row_00_01_00_10 : b4RowContribution (![0, 1, 1, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 11] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 11 = 13
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 11^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_10

theorem weighted_00_01_00_10 : b4RawGapContribution ![0, 1, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 0 :=
      b4GapContribution_from_row 0 1 0 10 0 row_00_01_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_10

theorem row_00_01_00_11 : b4RowContribution (![0, 1, 1, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 12] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 12 = 14
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 12^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_11

theorem weighted_00_01_00_11 : b4RawGapContribution ![0, 1, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 11] = b4GapPatternWeight 1 0 11 * 0 :=
      b4GapContribution_from_row 0 1 0 11 0 row_00_01_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_11

def layers_00_01_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_00_12

theorem cells_00_01_00_12 : QTableValid (![0, 1, 1, 13] : Fin 4 → ℕ) layers_00_01_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_00_12

theorem valid_00_01_00_12 :
    SparseRowValid (![0, 1, 1, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 1, 13] : Fin 4 → ℕ) i) = 15 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 1 + 13 = 15
      decide
    have hzsq : (∑ i, (((![0, 1, 1, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 1^2 + 13^2 = 171
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_00_12
#print axioms Paper7MomentGapNumeric.valid_00_01_00_12

def qvalues_00_01_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_00_12

theorem row_00_01_00_12 : b4RowContribution (![0, 1, 1, 13] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![0, 1, 1, 13] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_01_00_12) :=
      sparseRow_sound (![0, 1, 1, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_00_12) valid_00_01_00_12
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_00_12 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_00_12

theorem weighted_00_01_00_12 : b4RawGapContribution ![0, 1, 0, 12] = 48 := by
  calc
    b4RawGapContribution ![0, 1, 0, 12] = b4GapPatternWeight 1 0 12 * 4 :=
      b4GapContribution_from_row 0 1 0 12 4 row_00_01_00_12
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_12

theorem row_00_01_00_13 : b4RowContribution (![0, 1, 1, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 14] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 14 = 16
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 14^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_13

theorem weighted_00_01_00_13 : b4RawGapContribution ![0, 1, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 13] = b4GapPatternWeight 1 0 13 * 0 :=
      b4GapContribution_from_row 0 1 0 13 0 row_00_01_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_13

def layers_00_01_00_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_00_14

theorem cells_00_01_00_14 : QTableValid (![0, 1, 1, 15] : Fin 4 → ℕ) layers_00_01_00_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_00_14

theorem valid_00_01_00_14 :
    SparseRowValid (![0, 1, 1, 15] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_00_01_00_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 1, 15] : Fin 4 → ℕ) i) = 17 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 1 + 15 = 17
      decide
    have hzsq : (∑ i, (((![0, 1, 1, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 1^2 + 15^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_00_14
#print axioms Paper7MomentGapNumeric.valid_00_01_00_14

def qvalues_00_01_00_14 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_00_14

theorem row_00_01_00_14 : b4RowContribution (![0, 1, 1, 15] : Fin 4 → ℕ) = 5 := by
  calc
    b4RowContribution (![0, 1, 1, 15] : Fin 4 → ℕ) =
        sparseRowValue ({11, 17} : Finset (Fin 19)) (fun _ => layers_00_01_00_14) :=
      sparseRow_sound (![0, 1, 1, 15] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_00_01_00_14) valid_00_01_00_14
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_00_14 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 5 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_00_14

theorem weighted_00_01_00_14 : b4RawGapContribution ![0, 1, 0, 14] = 60 := by
  calc
    b4RawGapContribution ![0, 1, 0, 14] = b4GapPatternWeight 1 0 14 * 5 :=
      b4GapContribution_from_row 0 1 0 14 5 row_00_01_00_14
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_14

theorem row_00_01_00_15 : b4RowContribution (![0, 1, 1, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 16] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 16 = 18
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 16^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_15

theorem weighted_00_01_00_15 : b4RawGapContribution ![0, 1, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 15] = b4GapPatternWeight 1 0 15 * 0 :=
      b4GapContribution_from_row 0 1 0 15 0 row_00_01_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_15

def layers_00_01_00_16 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_00_16

theorem cells_00_01_00_16 : QTableValid (![0, 1, 1, 17] : Fin 4 → ℕ) layers_00_01_00_16 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_00_16

theorem valid_00_01_00_16 :
    SparseRowValid (![0, 1, 1, 17] : Fin 4 → ℕ) ({12, 18} : Finset (Fin 19)) (fun _ => layers_00_01_00_16) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 1, 17] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 1 + 17 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 1, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 1^2 + 17^2 = 291
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_00_16
#print axioms Paper7MomentGapNumeric.valid_00_01_00_16

def qvalues_00_01_00_16 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 3]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_00_16

theorem row_00_01_00_16 : b4RowContribution (![0, 1, 1, 17] : Fin 4 → ℕ) = 7 := by
  calc
    b4RowContribution (![0, 1, 1, 17] : Fin 4 → ℕ) =
        sparseRowValue ({12, 18} : Finset (Fin 19)) (fun _ => layers_00_01_00_16) :=
      sparseRow_sound (![0, 1, 1, 17] : Fin 4 → ℕ) ({12, 18} : Finset (Fin 19)) (fun _ => layers_00_01_00_16) valid_00_01_00_16
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_00_16 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
        _ = 7 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_00_16

theorem weighted_00_01_00_16 : b4RawGapContribution ![0, 1, 0, 16] = 84 := by
  calc
    b4RawGapContribution ![0, 1, 0, 16] = b4GapPatternWeight 1 0 16 * 7 :=
      b4GapContribution_from_row 0 1 0 16 7 row_00_01_00_16
    _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_16

theorem row_00_01_00_17 : b4RowContribution (![0, 1, 1, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 18] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 18 = 20
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 18^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_17

theorem weighted_00_01_00_17 : b4RawGapContribution ![0, 1, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 17] = b4GapPatternWeight 1 0 17 * 0 :=
      b4GapContribution_from_row 0 1 0 17 0 row_00_01_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_17

theorem row_00_01_00_18 : b4RowContribution (![0, 1, 1, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 19] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 19 = 21
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 19^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_18

theorem weighted_00_01_00_18 : b4RawGapContribution ![0, 1, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 18] = b4GapPatternWeight 1 0 18 * 0 :=
      b4GapContribution_from_row 0 1 0 18 0 row_00_01_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_18

theorem row_00_01_00_19 : b4RowContribution (![0, 1, 1, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 20] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 20 = 22
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 20^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_19

theorem weighted_00_01_00_19 : b4RawGapContribution ![0, 1, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 19] = b4GapPatternWeight 1 0 19 * 0 :=
      b4GapContribution_from_row 0 1 0 19 0 row_00_01_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_19

theorem row_00_01_00_20 : b4RowContribution (![0, 1, 1, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 21] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 21 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 21^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_20

theorem weighted_00_01_00_20 : b4RawGapContribution ![0, 1, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 20] = b4GapPatternWeight 1 0 20 * 0 :=
      b4GapContribution_from_row 0 1 0 20 0 row_00_01_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_20

theorem row_00_01_00_21 : b4RowContribution (![0, 1, 1, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 22] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 22 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 22^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_21

theorem weighted_00_01_00_21 : b4RawGapContribution ![0, 1, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 21] = b4GapPatternWeight 1 0 21 * 0 :=
      b4GapContribution_from_row 0 1 0 21 0 row_00_01_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_21

theorem row_00_01_00_22 : b4RowContribution (![0, 1, 1, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 23] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 23 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 23^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_22

theorem weighted_00_01_00_22 : b4RawGapContribution ![0, 1, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 22] = b4GapPatternWeight 1 0 22 * 0 :=
      b4GapContribution_from_row 0 1 0 22 0 row_00_01_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_22

def layers_00_01_00_23 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]]
#print axioms Paper7MomentGapNumeric.layers_00_01_00_23

theorem cells_00_01_00_23 : QTableValid (![0, 1, 1, 24] : Fin 4 → ℕ) layers_00_01_00_23 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_00_23

theorem valid_00_01_00_23 :
    SparseRowValid (![0, 1, 1, 24] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_01_00_23) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 1, 24] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 1 + 24 = 26
      decide
    have hzsq : (∑ i, (((![0, 1, 1, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 1^2 + 24^2 = 578
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_00_23
#print axioms Paper7MomentGapNumeric.valid_00_01_00_23

def qvalues_00_01_00_23 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_00_23

theorem row_00_01_00_23 : b4RowContribution (![0, 1, 1, 24] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![0, 1, 1, 24] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_01_00_23) :=
      sparseRow_sound (![0, 1, 1, 24] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_01_00_23) valid_00_01_00_23
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_00_23 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_00_23

theorem weighted_00_01_00_23 : b4RawGapContribution ![0, 1, 0, 23] = 48 := by
  calc
    b4RawGapContribution ![0, 1, 0, 23] = b4GapPatternWeight 1 0 23 * 4 :=
      b4GapContribution_from_row 0 1 0 23 4 row_00_01_00_23
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_23

theorem row_00_01_00_24 : b4RowContribution (![0, 1, 1, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 25] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 25 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 627 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 25^2 = 627
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_24

theorem weighted_00_01_00_24 : b4RawGapContribution ![0, 1, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 24] = b4GapPatternWeight 1 0 24 * 0 :=
      b4GapContribution_from_row 0 1 0 24 0 row_00_01_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_24

theorem row_00_01_00_25 : b4RowContribution (![0, 1, 1, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 26] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 26 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 678 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 26^2 = 678
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_25

theorem weighted_00_01_00_25 : b4RawGapContribution ![0, 1, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 25] = b4GapPatternWeight 1 0 25 * 0 :=
      b4GapContribution_from_row 0 1 0 25 0 row_00_01_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_25

theorem row_00_01_00_26 : b4RowContribution (![0, 1, 1, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 27] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 27 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 731 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 27^2 = 731
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_26

theorem weighted_00_01_00_26 : b4RawGapContribution ![0, 1, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 26] = b4GapPatternWeight 1 0 26 * 0 :=
      b4GapContribution_from_row 0 1 0 26 0 row_00_01_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_26

theorem row_00_01_00_27 : b4RowContribution (![0, 1, 1, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 28] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 28 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 786 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 28^2 = 786
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_27

theorem weighted_00_01_00_27 : b4RawGapContribution ![0, 1, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 27] = b4GapPatternWeight 1 0 27 * 0 :=
      b4GapContribution_from_row 0 1 0 27 0 row_00_01_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_27

theorem row_00_01_00_28 : b4RowContribution (![0, 1, 1, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 29] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 29 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 843 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 29^2 = 843
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_28

theorem weighted_00_01_00_28 : b4RawGapContribution ![0, 1, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 28] = b4GapPatternWeight 1 0 28 * 0 :=
      b4GapContribution_from_row 0 1 0 28 0 row_00_01_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_28

theorem row_00_01_00_29 : b4RowContribution (![0, 1, 1, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 30] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 30 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 902 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 30^2 = 902
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_29

theorem weighted_00_01_00_29 : b4RawGapContribution ![0, 1, 0, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 29] = b4GapPatternWeight 1 0 29 * 0 :=
      b4GapContribution_from_row 0 1 0 29 0 row_00_01_00_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_29

theorem row_00_01_00_30 : b4RowContribution (![0, 1, 1, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 31] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 31 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 963 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 31^2 = 963
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_30

theorem weighted_00_01_00_30 : b4RawGapContribution ![0, 1, 0, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 30] = b4GapPatternWeight 1 0 30 * 0 :=
      b4GapContribution_from_row 0 1 0 30 0 row_00_01_00_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_30

theorem row_00_01_00_31 : b4RowContribution (![0, 1, 1, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 32] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 32 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1026 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 32^2 = 1026
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_31

theorem weighted_00_01_00_31 : b4RawGapContribution ![0, 1, 0, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 31] = b4GapPatternWeight 1 0 31 * 0 :=
      b4GapContribution_from_row 0 1 0 31 0 row_00_01_00_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_31

theorem row_00_01_00_32 : b4RowContribution (![0, 1, 1, 33] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 33] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 33 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1091 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 33^2 = 1091
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_32

theorem weighted_00_01_00_32 : b4RawGapContribution ![0, 1, 0, 32] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 32] = b4GapPatternWeight 1 0 32 * 0 :=
      b4GapContribution_from_row 0 1 0 32 0 row_00_01_00_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_32

theorem row_00_01_00_33 : b4RowContribution (![0, 1, 1, 34] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 34] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 34 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1158 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 34^2 = 1158
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_33

theorem weighted_00_01_00_33 : b4RawGapContribution ![0, 1, 0, 33] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 33] = b4GapPatternWeight 1 0 33 * 0 :=
      b4GapContribution_from_row 0 1 0 33 0 row_00_01_00_33
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_33

theorem row_00_01_00_34 : b4RowContribution (![0, 1, 1, 35] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 1, 35] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 1 + 35 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 1, 35] : Fin 4 → ℕ) i : ℤ)^2)) = 1227 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 1^2 + 35^2 = 1227
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_00_34

theorem weighted_00_01_00_34 : b4RawGapContribution ![0, 1, 0, 34] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 0, 34] = b4GapPatternWeight 1 0 34 * 0 :=
      b4GapContribution_from_row 0 1 0 34 0 row_00_01_00_34
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_00_34

def dvalues_00_01_00 : Fin 35 → ℕ := ![0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 48, 0, 60, 0, 84, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_00

theorem dblock_00_01_00 : b4GapPatternDBlock 0 1 0 = 288 := by
  calc
    b4GapPatternDBlock 0 1 0 = ∑ d : Fin 35, dvalues_00_01_00 d := by
      apply b4GapDBlock_of_rows 0 1 0 dvalues_00_01_00
      intro d
      fin_cases d
      · exact weighted_00_01_00_00
      · exact weighted_00_01_00_01
      · exact weighted_00_01_00_02
      · exact weighted_00_01_00_03
      · exact weighted_00_01_00_04
      · exact weighted_00_01_00_05
      · exact weighted_00_01_00_06
      · exact weighted_00_01_00_07
      · exact weighted_00_01_00_08
      · exact weighted_00_01_00_09
      · exact weighted_00_01_00_10
      · exact weighted_00_01_00_11
      · exact weighted_00_01_00_12
      · exact weighted_00_01_00_13
      · exact weighted_00_01_00_14
      · exact weighted_00_01_00_15
      · exact weighted_00_01_00_16
      · exact weighted_00_01_00_17
      · exact weighted_00_01_00_18
      · exact weighted_00_01_00_19
      · exact weighted_00_01_00_20
      · exact weighted_00_01_00_21
      · exact weighted_00_01_00_22
      · exact weighted_00_01_00_23
      · exact weighted_00_01_00_24
      · exact weighted_00_01_00_25
      · exact weighted_00_01_00_26
      · exact weighted_00_01_00_27
      · exact weighted_00_01_00_28
      · exact weighted_00_01_00_29
      · exact weighted_00_01_00_30
      · exact weighted_00_01_00_31
      · exact weighted_00_01_00_32
      · exact weighted_00_01_00_33
      · exact weighted_00_01_00_34
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_00

end Paper7MomentGapNumeric
