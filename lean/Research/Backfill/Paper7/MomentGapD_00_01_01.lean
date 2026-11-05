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

theorem row_00_01_01_00 : b4RowContribution (![0, 1, 2, 2] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 2] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 2 = 5
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 9 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 2^2 = 9
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_00

theorem weighted_00_01_01_00 : b4RawGapContribution ![0, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 0 1 1 0 0 row_00_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_00

theorem row_00_01_01_01 : b4RowContribution (![0, 1, 2, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 3] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 3 = 6
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 14 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 3^2 = 14
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_01

theorem weighted_00_01_01_01 : b4RawGapContribution ![0, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 0 1 1 1 0 row_00_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_01

theorem row_00_01_01_02 : b4RowContribution (![0, 1, 2, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 4] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 4 = 7
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 21 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 4^2 = 21
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_02

theorem weighted_00_01_01_02 : b4RawGapContribution ![0, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 0 1 1 2 0 row_00_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_02

theorem row_00_01_01_03 : b4RowContribution (![0, 1, 2, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 5] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 5 = 8
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 30 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 5^2 = 30
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_03

theorem weighted_00_01_01_03 : b4RawGapContribution ![0, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 0 1 1 3 0 row_00_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_03

def layers_00_01_01_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_01_04

theorem cells_00_01_01_04 : QTableValid (![0, 1, 2, 6] : Fin 4 → ℕ) layers_00_01_01_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_01_04

theorem valid_00_01_01_04 :
    SparseRowValid (![0, 1, 2, 6] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_01_01_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 2, 6] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 2 + 6 = 9
      decide
    have hzsq : (∑ i, (((![0, 1, 2, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 41 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 2^2 + 6^2 = 41
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_01_04
#print axioms Paper7MomentGapNumeric.valid_00_01_01_04

def qvalues_00_01_01_04 : Fin 19 → ℕ := ![0, 0, 5, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_01_04

theorem row_00_01_01_04 : b4RowContribution (![0, 1, 2, 6] : Fin 4 → ℕ) = 8 := by
  calc
    b4RowContribution (![0, 1, 2, 6] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_01_01_04) :=
      sparseRow_sound (![0, 1, 2, 6] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_01_01_04) valid_00_01_01_04
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_01_04 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_01_04

theorem weighted_00_01_01_04 : b4RawGapContribution ![0, 1, 1, 4] = 192 := by
  calc
    b4RawGapContribution ![0, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 8 :=
      b4GapContribution_from_row 0 1 1 4 8 row_00_01_01_04
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_04

theorem row_00_01_01_05 : b4RowContribution (![0, 1, 2, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 7] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 7 = 10
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 54 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 7^2 = 54
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_05

theorem weighted_00_01_01_05 : b4RawGapContribution ![0, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 0 1 1 5 0 row_00_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_05

theorem row_00_01_01_06 : b4RowContribution (![0, 1, 2, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 8] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 8 = 11
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 69 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 8^2 = 69
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_06

theorem weighted_00_01_01_06 : b4RawGapContribution ![0, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 0 1 1 6 0 row_00_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_06

theorem row_00_01_01_07 : b4RowContribution (![0, 1, 2, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 9] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 9 = 12
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 86 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 9^2 = 86
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_07

theorem weighted_00_01_01_07 : b4RawGapContribution ![0, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 0 1 1 7 0 row_00_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_07

theorem row_00_01_01_08 : b4RowContribution (![0, 1, 2, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 10] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 10 = 13
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 105 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 10^2 = 105
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_08

theorem weighted_00_01_01_08 : b4RawGapContribution ![0, 1, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 0 :=
      b4GapContribution_from_row 0 1 1 8 0 row_00_01_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_08

theorem row_00_01_01_09 : b4RowContribution (![0, 1, 2, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 11] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 11 = 14
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 11^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_09

theorem weighted_00_01_01_09 : b4RawGapContribution ![0, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 0 1 1 9 0 row_00_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_09

theorem row_00_01_01_10 : b4RowContribution (![0, 1, 2, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 12] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 12 = 15
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 12^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_10

theorem weighted_00_01_01_10 : b4RawGapContribution ![0, 1, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 0 :=
      b4GapContribution_from_row 0 1 1 10 0 row_00_01_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_10

def layers_00_01_01_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_01_01_11

theorem cells_00_01_01_11 : QTableValid (![0, 1, 2, 13] : Fin 4 → ℕ) layers_00_01_01_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_01_11

theorem valid_00_01_01_11 :
    SparseRowValid (![0, 1, 2, 13] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_01_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 2, 13] : Fin 4 → ℕ) i) = 16 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 2 + 13 = 16
      decide
    have hzsq : (∑ i, (((![0, 1, 2, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 2^2 + 13^2 = 174
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_01_11
#print axioms Paper7MomentGapNumeric.valid_00_01_01_11

def qvalues_00_01_01_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_01_11

theorem row_00_01_01_11 : b4RowContribution (![0, 1, 2, 13] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 1, 2, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_01_11) :=
      sparseRow_sound (![0, 1, 2, 13] : Fin 4 → ℕ) ({9, 15} : Finset (Fin 19)) (fun _ => layers_00_01_01_11) valid_00_01_01_11
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_01_11 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_01_11

theorem weighted_00_01_01_11 : b4RawGapContribution ![0, 1, 1, 11] = 216 := by
  calc
    b4RawGapContribution ![0, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 9 :=
      b4GapContribution_from_row 0 1 1 11 9 row_00_01_01_11
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_11

theorem row_00_01_01_12 : b4RowContribution (![0, 1, 2, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 14] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 14 = 17
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 14^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_12

theorem weighted_00_01_01_12 : b4RawGapContribution ![0, 1, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 0 :=
      b4GapContribution_from_row 0 1 1 12 0 row_00_01_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_12

def layers_00_01_01_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1]]
#print axioms Paper7MomentGapNumeric.layers_00_01_01_13

theorem cells_00_01_01_13 : QTableValid (![0, 1, 2, 15] : Fin 4 → ℕ) layers_00_01_01_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_01_13

theorem valid_00_01_01_13 :
    SparseRowValid (![0, 1, 2, 15] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_01_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 2, 15] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 2 + 15 = 18
      decide
    have hzsq : (∑ i, (((![0, 1, 2, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 2^2 + 15^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_01_13
#print axioms Paper7MomentGapNumeric.valid_00_01_01_13

def qvalues_00_01_01_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_01_13

theorem row_00_01_01_13 : b4RowContribution (![0, 1, 2, 15] : Fin 4 → ℕ) = 12 := by
  calc
    b4RowContribution (![0, 1, 2, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_01_13) :=
      sparseRow_sound (![0, 1, 2, 15] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_00_01_01_13) valid_00_01_01_13
    _ = 12 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_01_13 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_01_13

theorem weighted_00_01_01_13 : b4RawGapContribution ![0, 1, 1, 13] = 288 := by
  calc
    b4RawGapContribution ![0, 1, 1, 13] = b4GapPatternWeight 1 1 13 * 12 :=
      b4GapContribution_from_row 0 1 1 13 12 row_00_01_01_13
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_13

theorem row_00_01_01_14 : b4RowContribution (![0, 1, 2, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 16] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 16 = 19
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 16^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_14

theorem weighted_00_01_01_14 : b4RawGapContribution ![0, 1, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 14] = b4GapPatternWeight 1 1 14 * 0 :=
      b4GapContribution_from_row 0 1 1 14 0 row_00_01_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_14

def layers_00_01_01_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5]]
#print axioms Paper7MomentGapNumeric.layers_00_01_01_15

theorem cells_00_01_01_15 : QTableValid (![0, 1, 2, 17] : Fin 4 → ℕ) layers_00_01_01_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_01_15

theorem valid_00_01_01_15 :
    SparseRowValid (![0, 1, 2, 17] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_01_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 2, 17] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 2 + 17 = 20
      decide
    have hzsq : (∑ i, (((![0, 1, 2, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 2^2 + 17^2 = 294
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_01_15
#print axioms Paper7MomentGapNumeric.valid_00_01_01_15

def qvalues_00_01_01_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_01_15

theorem row_00_01_01_15 : b4RowContribution (![0, 1, 2, 17] : Fin 4 → ℕ) = 6 := by
  calc
    b4RowContribution (![0, 1, 2, 17] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_00_01_01_15) :=
      sparseRow_sound (![0, 1, 2, 17] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_01_15) valid_00_01_01_15
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_01_15 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_01_15

theorem weighted_00_01_01_15 : b4RawGapContribution ![0, 1, 1, 15] = 144 := by
  calc
    b4RawGapContribution ![0, 1, 1, 15] = b4GapPatternWeight 1 1 15 * 6 :=
      b4GapContribution_from_row 0 1 1 15 6 row_00_01_01_15
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_15

theorem row_00_01_01_16 : b4RowContribution (![0, 1, 2, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 18] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 18 = 21
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 18^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_16

theorem weighted_00_01_01_16 : b4RawGapContribution ![0, 1, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 16] = b4GapPatternWeight 1 1 16 * 0 :=
      b4GapContribution_from_row 0 1 1 16 0 row_00_01_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_16

theorem row_00_01_01_17 : b4RowContribution (![0, 1, 2, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 19] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 19 = 22
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 19^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_17

theorem weighted_00_01_01_17 : b4RawGapContribution ![0, 1, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 17] = b4GapPatternWeight 1 1 17 * 0 :=
      b4GapContribution_from_row 0 1 1 17 0 row_00_01_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_17

theorem row_00_01_01_18 : b4RowContribution (![0, 1, 2, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 20] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 20 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 20^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_18

theorem weighted_00_01_01_18 : b4RawGapContribution ![0, 1, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 18] = b4GapPatternWeight 1 1 18 * 0 :=
      b4GapContribution_from_row 0 1 1 18 0 row_00_01_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_18

theorem row_00_01_01_19 : b4RowContribution (![0, 1, 2, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 21] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 21 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 21^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_19

theorem weighted_00_01_01_19 : b4RawGapContribution ![0, 1, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 19] = b4GapPatternWeight 1 1 19 * 0 :=
      b4GapContribution_from_row 0 1 1 19 0 row_00_01_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_19

theorem row_00_01_01_20 : b4RowContribution (![0, 1, 2, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 22] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 22 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 22^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_20

theorem weighted_00_01_01_20 : b4RawGapContribution ![0, 1, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 20] = b4GapPatternWeight 1 1 20 * 0 :=
      b4GapContribution_from_row 0 1 1 20 0 row_00_01_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_20

theorem row_00_01_01_21 : b4RowContribution (![0, 1, 2, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 23] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 23 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 23^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_21

theorem weighted_00_01_01_21 : b4RawGapContribution ![0, 1, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 21] = b4GapPatternWeight 1 1 21 * 0 :=
      b4GapContribution_from_row 0 1 1 21 0 row_00_01_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_21

theorem row_00_01_01_22 : b4RowContribution (![0, 1, 2, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 24] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 24 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 581 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 24^2 = 581
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_22

theorem weighted_00_01_01_22 : b4RawGapContribution ![0, 1, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 22] = b4GapPatternWeight 1 1 22 * 0 :=
      b4GapContribution_from_row 0 1 1 22 0 row_00_01_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_22

theorem row_00_01_01_23 : b4RowContribution (![0, 1, 2, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 25] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 25 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 630 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 25^2 = 630
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_23

theorem weighted_00_01_01_23 : b4RawGapContribution ![0, 1, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 23] = b4GapPatternWeight 1 1 23 * 0 :=
      b4GapContribution_from_row 0 1 1 23 0 row_00_01_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_23

theorem row_00_01_01_24 : b4RowContribution (![0, 1, 2, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 26] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 26 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 681 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 26^2 = 681
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_24

theorem weighted_00_01_01_24 : b4RawGapContribution ![0, 1, 1, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 24] = b4GapPatternWeight 1 1 24 * 0 :=
      b4GapContribution_from_row 0 1 1 24 0 row_00_01_01_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_24

theorem row_00_01_01_25 : b4RowContribution (![0, 1, 2, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 27] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 27 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 734 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 27^2 = 734
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_25

theorem weighted_00_01_01_25 : b4RawGapContribution ![0, 1, 1, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 25] = b4GapPatternWeight 1 1 25 * 0 :=
      b4GapContribution_from_row 0 1 1 25 0 row_00_01_01_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_25

theorem row_00_01_01_26 : b4RowContribution (![0, 1, 2, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 28] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 28 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 789 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 28^2 = 789
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_26

theorem weighted_00_01_01_26 : b4RawGapContribution ![0, 1, 1, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 26] = b4GapPatternWeight 1 1 26 * 0 :=
      b4GapContribution_from_row 0 1 1 26 0 row_00_01_01_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_26

theorem row_00_01_01_27 : b4RowContribution (![0, 1, 2, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 29] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 29 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 846 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 29^2 = 846
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_27

theorem weighted_00_01_01_27 : b4RawGapContribution ![0, 1, 1, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 27] = b4GapPatternWeight 1 1 27 * 0 :=
      b4GapContribution_from_row 0 1 1 27 0 row_00_01_01_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_27

theorem row_00_01_01_28 : b4RowContribution (![0, 1, 2, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 30] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 30 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 905 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 30^2 = 905
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_28

theorem weighted_00_01_01_28 : b4RawGapContribution ![0, 1, 1, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 28] = b4GapPatternWeight 1 1 28 * 0 :=
      b4GapContribution_from_row 0 1 1 28 0 row_00_01_01_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_28

theorem row_00_01_01_29 : b4RowContribution (![0, 1, 2, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 31] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 31 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 966 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 31^2 = 966
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_29

theorem weighted_00_01_01_29 : b4RawGapContribution ![0, 1, 1, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 29] = b4GapPatternWeight 1 1 29 * 0 :=
      b4GapContribution_from_row 0 1 1 29 0 row_00_01_01_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_29

theorem row_00_01_01_30 : b4RowContribution (![0, 1, 2, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 32] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 32 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1029 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 32^2 = 1029
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_30

theorem weighted_00_01_01_30 : b4RawGapContribution ![0, 1, 1, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 30] = b4GapPatternWeight 1 1 30 * 0 :=
      b4GapContribution_from_row 0 1 1 30 0 row_00_01_01_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_30

theorem row_00_01_01_31 : b4RowContribution (![0, 1, 2, 33] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 33] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 33 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1094 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 33^2 = 1094
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_31

theorem weighted_00_01_01_31 : b4RawGapContribution ![0, 1, 1, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 31] = b4GapPatternWeight 1 1 31 * 0 :=
      b4GapContribution_from_row 0 1 1 31 0 row_00_01_01_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_31

theorem row_00_01_01_32 : b4RowContribution (![0, 1, 2, 34] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 2, 34] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 2 + 34 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 2, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1161 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 2^2 + 34^2 = 1161
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_01_32

theorem weighted_00_01_01_32 : b4RawGapContribution ![0, 1, 1, 32] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 1, 32] = b4GapPatternWeight 1 1 32 * 0 :=
      b4GapContribution_from_row 0 1 1 32 0 row_00_01_01_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_01_32

def dvalues_00_01_01 : Fin 33 → ℕ := ![0, 0, 0, 0, 192, 0, 0, 0, 0, 0, 0, 216, 0, 288, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_01

theorem dblock_00_01_01 : b4GapPatternDBlock 0 1 1 = 840 := by
  calc
    b4GapPatternDBlock 0 1 1 = ∑ d : Fin 33, dvalues_00_01_01 d := by
      apply b4GapDBlock_of_rows 0 1 1 dvalues_00_01_01
      intro d
      fin_cases d
      · exact weighted_00_01_01_00
      · exact weighted_00_01_01_01
      · exact weighted_00_01_01_02
      · exact weighted_00_01_01_03
      · exact weighted_00_01_01_04
      · exact weighted_00_01_01_05
      · exact weighted_00_01_01_06
      · exact weighted_00_01_01_07
      · exact weighted_00_01_01_08
      · exact weighted_00_01_01_09
      · exact weighted_00_01_01_10
      · exact weighted_00_01_01_11
      · exact weighted_00_01_01_12
      · exact weighted_00_01_01_13
      · exact weighted_00_01_01_14
      · exact weighted_00_01_01_15
      · exact weighted_00_01_01_16
      · exact weighted_00_01_01_17
      · exact weighted_00_01_01_18
      · exact weighted_00_01_01_19
      · exact weighted_00_01_01_20
      · exact weighted_00_01_01_21
      · exact weighted_00_01_01_22
      · exact weighted_00_01_01_23
      · exact weighted_00_01_01_24
      · exact weighted_00_01_01_25
      · exact weighted_00_01_01_26
      · exact weighted_00_01_01_27
      · exact weighted_00_01_01_28
      · exact weighted_00_01_01_29
      · exact weighted_00_01_01_30
      · exact weighted_00_01_01_31
      · exact weighted_00_01_01_32
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_01

end Paper7MomentGapNumeric
