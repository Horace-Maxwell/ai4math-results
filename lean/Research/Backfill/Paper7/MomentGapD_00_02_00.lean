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

theorem row_00_02_00_00 : b4RowContribution (![0, 2, 2, 2] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 2] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 2 = 6
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 12 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 2^2 = 12
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_00

theorem weighted_00_02_00_00 : b4RawGapContribution ![0, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 0 2 0 0 0 row_00_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_00

theorem row_00_02_00_01 : b4RowContribution (![0, 2, 2, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 3] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 3 = 7
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 17 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 3^2 = 17
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_01

theorem weighted_00_02_00_01 : b4RawGapContribution ![0, 2, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 0 :=
      b4GapContribution_from_row 0 2 0 1 0 row_00_02_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_01

theorem row_00_02_00_02 : b4RowContribution (![0, 2, 2, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 4] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 4 = 8
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 24 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 4^2 = 24
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_02

theorem weighted_00_02_00_02 : b4RawGapContribution ![0, 2, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 0 :=
      b4GapContribution_from_row 0 2 0 2 0 row_00_02_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_02

def layers_00_02_00_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_02_00_03

theorem cells_00_02_00_03 : QTableValid (![0, 2, 2, 5] : Fin 4 → ℕ) layers_00_02_00_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_00_03

theorem valid_00_02_00_03 :
    SparseRowValid (![0, 2, 2, 5] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_00_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 2, 5] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 2 + 5 = 9
      decide
    have hzsq : (∑ i, (((![0, 2, 2, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 33 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 2^2 + 5^2 = 33
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_00_03
#print axioms Paper7MomentGapNumeric.valid_00_02_00_03

def qvalues_00_02_00_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_00_03

theorem row_00_02_00_03 : b4RowContribution (![0, 2, 2, 5] : Fin 4 → ℕ) = 8 := by
  calc
    b4RowContribution (![0, 2, 2, 5] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_02_00_03) :=
      sparseRow_sound (![0, 2, 2, 5] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_02_00_03) valid_00_02_00_03
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_00_03 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_00_03

theorem weighted_00_02_00_03 : b4RawGapContribution ![0, 2, 0, 3] = 96 := by
  calc
    b4RawGapContribution ![0, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 8 :=
      b4GapContribution_from_row 0 2 0 3 8 row_00_02_00_03
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_03

def layers_00_02_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_02_00_04

theorem cells_00_02_00_04 : QTableValid (![0, 2, 2, 6] : Fin 4 → ℕ) layers_00_02_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_00_04

theorem valid_00_02_00_04 :
    SparseRowValid (![0, 2, 2, 6] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_02_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 2, 6] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 2 + 6 = 10
      decide
    have hzsq : (∑ i, (((![0, 2, 2, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 44 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 2^2 + 6^2 = 44
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_00_04
#print axioms Paper7MomentGapNumeric.valid_00_02_00_04

def qvalues_00_02_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_00_04

theorem row_00_02_00_04 : b4RowContribution (![0, 2, 2, 6] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 2, 2, 6] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_02_00_04) :=
      sparseRow_sound (![0, 2, 2, 6] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_02_00_04) valid_00_02_00_04
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_00_04 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_00_04

theorem weighted_00_02_00_04 : b4RawGapContribution ![0, 2, 0, 4] = 108 := by
  calc
    b4RawGapContribution ![0, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 9 :=
      b4GapContribution_from_row 0 2 0 4 9 row_00_02_00_04
    _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_04

theorem row_00_02_00_05 : b4RowContribution (![0, 2, 2, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 7] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 7 = 11
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 57 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 7^2 = 57
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_05

theorem weighted_00_02_00_05 : b4RawGapContribution ![0, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 0 2 0 5 0 row_00_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_05

theorem row_00_02_00_06 : b4RowContribution (![0, 2, 2, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 8] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 8 = 12
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 72 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 8^2 = 72
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_06

theorem weighted_00_02_00_06 : b4RawGapContribution ![0, 2, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 0 :=
      b4GapContribution_from_row 0 2 0 6 0 row_00_02_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_06

theorem row_00_02_00_07 : b4RowContribution (![0, 2, 2, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 9] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 9 = 13
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 89 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 9^2 = 89
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_07

theorem weighted_00_02_00_07 : b4RawGapContribution ![0, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 0 2 0 7 0 row_00_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_07

theorem row_00_02_00_08 : b4RowContribution (![0, 2, 2, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 10] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 10 = 14
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 10^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_08

theorem weighted_00_02_00_08 : b4RawGapContribution ![0, 2, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 8] = b4GapPatternWeight 2 0 8 * 0 :=
      b4GapContribution_from_row 0 2 0 8 0 row_00_02_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_08

theorem row_00_02_00_09 : b4RowContribution (![0, 2, 2, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 11] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 11 = 15
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 11^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_09

theorem weighted_00_02_00_09 : b4RawGapContribution ![0, 2, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 9] = b4GapPatternWeight 2 0 9 * 0 :=
      b4GapContribution_from_row 0 2 0 9 0 row_00_02_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_09

theorem row_00_02_00_10 : b4RowContribution (![0, 2, 2, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 12] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 12 = 16
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 152 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 12^2 = 152
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_10

theorem weighted_00_02_00_10 : b4RawGapContribution ![0, 2, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 10] = b4GapPatternWeight 2 0 10 * 0 :=
      b4GapContribution_from_row 0 2 0 10 0 row_00_02_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_10

def layers_00_02_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_02_00_11

theorem cells_00_02_00_11 : QTableValid (![0, 2, 2, 13] : Fin 4 → ℕ) layers_00_02_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_00_11

theorem valid_00_02_00_11 :
    SparseRowValid (![0, 2, 2, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 2, 13] : Fin 4 → ℕ) i) = 17 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 2 + 13 = 17
      decide
    have hzsq : (∑ i, (((![0, 2, 2, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 2^2 + 13^2 = 177
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_00_11
#print axioms Paper7MomentGapNumeric.valid_00_02_00_11

def qvalues_00_02_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_00_11

theorem row_00_02_00_11 : b4RowContribution (![0, 2, 2, 13] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 2, 2, 13] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_02_00_11) :=
      sparseRow_sound (![0, 2, 2, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_00_11) valid_00_02_00_11
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_00_11 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_00_11

theorem weighted_00_02_00_11 : b4RawGapContribution ![0, 2, 0, 11] = 108 := by
  calc
    b4RawGapContribution ![0, 2, 0, 11] = b4GapPatternWeight 2 0 11 * 9 :=
      b4GapContribution_from_row 0 2 0 11 9 row_00_02_00_11
    _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_11

theorem row_00_02_00_12 : b4RowContribution (![0, 2, 2, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 14] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 14 = 18
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 14^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_12

theorem weighted_00_02_00_12 : b4RawGapContribution ![0, 2, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 12] = b4GapPatternWeight 2 0 12 * 0 :=
      b4GapContribution_from_row 0 2 0 12 0 row_00_02_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_12

def layers_00_02_00_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 6, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_02_00_13

theorem cells_00_02_00_13 : QTableValid (![0, 2, 2, 15] : Fin 4 → ℕ) layers_00_02_00_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_00_13

theorem valid_00_02_00_13 :
    SparseRowValid (![0, 2, 2, 15] : Fin 4 → ℕ) ({5, 11, 17} : Finset (Fin 19)) (fun _ => layers_00_02_00_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 2, 15] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 2 + 15 = 19
      decide
    have hzsq : (∑ i, (((![0, 2, 2, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 2^2 + 15^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_00_13
#print axioms Paper7MomentGapNumeric.valid_00_02_00_13

def qvalues_00_02_00_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 6, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_00_13

theorem row_00_02_00_13 : b4RowContribution (![0, 2, 2, 15] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 2, 15] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11, 17} : Finset (Fin 19)) (fun _ => layers_00_02_00_13) :=
      sparseRow_sound (![0, 2, 2, 15] : Fin 4 → ℕ) ({5, 11, 17} : Finset (Fin 19)) (fun _ => layers_00_02_00_13) valid_00_02_00_13
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_00_13 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_00_13

theorem weighted_00_02_00_13 : b4RawGapContribution ![0, 2, 0, 13] = 288 := by
  calc
    b4RawGapContribution ![0, 2, 0, 13] = b4GapPatternWeight 2 0 13 * 24 :=
      b4GapContribution_from_row 0 2 0 13 24 row_00_02_00_13
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_13

theorem row_00_02_00_14 : b4RowContribution (![0, 2, 2, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 16] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 16 = 20
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 264 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 16^2 = 264
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_14

theorem weighted_00_02_00_14 : b4RawGapContribution ![0, 2, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 14] = b4GapPatternWeight 2 0 14 * 0 :=
      b4GapContribution_from_row 0 2 0 14 0 row_00_02_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_14

theorem row_00_02_00_15 : b4RowContribution (![0, 2, 2, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 17] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 17 = 21
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 17^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_15

theorem weighted_00_02_00_15 : b4RawGapContribution ![0, 2, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 15] = b4GapPatternWeight 2 0 15 * 0 :=
      b4GapContribution_from_row 0 2 0 15 0 row_00_02_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_15

theorem row_00_02_00_16 : b4RowContribution (![0, 2, 2, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 18] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 18 = 22
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 18^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_16

theorem weighted_00_02_00_16 : b4RawGapContribution ![0, 2, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 16] = b4GapPatternWeight 2 0 16 * 0 :=
      b4GapContribution_from_row 0 2 0 16 0 row_00_02_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_16

theorem row_00_02_00_17 : b4RowContribution (![0, 2, 2, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 19] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 19 = 23
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 19^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_17

theorem weighted_00_02_00_17 : b4RawGapContribution ![0, 2, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 17] = b4GapPatternWeight 2 0 17 * 0 :=
      b4GapContribution_from_row 0 2 0 17 0 row_00_02_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_17

theorem row_00_02_00_18 : b4RowContribution (![0, 2, 2, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 20] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 20 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 408 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 20^2 = 408
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_18

theorem weighted_00_02_00_18 : b4RawGapContribution ![0, 2, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 18] = b4GapPatternWeight 2 0 18 * 0 :=
      b4GapContribution_from_row 0 2 0 18 0 row_00_02_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_18

theorem row_00_02_00_19 : b4RowContribution (![0, 2, 2, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 21] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 21 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 21^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_19

theorem weighted_00_02_00_19 : b4RawGapContribution ![0, 2, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 19] = b4GapPatternWeight 2 0 19 * 0 :=
      b4GapContribution_from_row 0 2 0 19 0 row_00_02_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_19

theorem row_00_02_00_20 : b4RowContribution (![0, 2, 2, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 22] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 22 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 492 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 22^2 = 492
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_20

theorem weighted_00_02_00_20 : b4RawGapContribution ![0, 2, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 20] = b4GapPatternWeight 2 0 20 * 0 :=
      b4GapContribution_from_row 0 2 0 20 0 row_00_02_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_20

theorem row_00_02_00_21 : b4RowContribution (![0, 2, 2, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 23] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 23 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 537 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 23^2 = 537
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_21

theorem weighted_00_02_00_21 : b4RawGapContribution ![0, 2, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 21] = b4GapPatternWeight 2 0 21 * 0 :=
      b4GapContribution_from_row 0 2 0 21 0 row_00_02_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_21

theorem row_00_02_00_22 : b4RowContribution (![0, 2, 2, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 24] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 24 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 584 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 24^2 = 584
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_22

theorem weighted_00_02_00_22 : b4RawGapContribution ![0, 2, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 22] = b4GapPatternWeight 2 0 22 * 0 :=
      b4GapContribution_from_row 0 2 0 22 0 row_00_02_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_22

theorem row_00_02_00_23 : b4RowContribution (![0, 2, 2, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 25] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 25 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 633 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 25^2 = 633
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_23

theorem weighted_00_02_00_23 : b4RawGapContribution ![0, 2, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 23] = b4GapPatternWeight 2 0 23 * 0 :=
      b4GapContribution_from_row 0 2 0 23 0 row_00_02_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_23

theorem row_00_02_00_24 : b4RowContribution (![0, 2, 2, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 26] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 26 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 684 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 26^2 = 684
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_24

theorem weighted_00_02_00_24 : b4RawGapContribution ![0, 2, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 24] = b4GapPatternWeight 2 0 24 * 0 :=
      b4GapContribution_from_row 0 2 0 24 0 row_00_02_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_24

theorem row_00_02_00_25 : b4RowContribution (![0, 2, 2, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 27] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 27 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 737 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 27^2 = 737
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_25

theorem weighted_00_02_00_25 : b4RawGapContribution ![0, 2, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 25] = b4GapPatternWeight 2 0 25 * 0 :=
      b4GapContribution_from_row 0 2 0 25 0 row_00_02_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_25

theorem row_00_02_00_26 : b4RowContribution (![0, 2, 2, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 28] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 28 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 792 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 28^2 = 792
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_26

theorem weighted_00_02_00_26 : b4RawGapContribution ![0, 2, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 26] = b4GapPatternWeight 2 0 26 * 0 :=
      b4GapContribution_from_row 0 2 0 26 0 row_00_02_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_26

theorem row_00_02_00_27 : b4RowContribution (![0, 2, 2, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 29] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 29 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 849 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 29^2 = 849
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_27

theorem weighted_00_02_00_27 : b4RawGapContribution ![0, 2, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 27] = b4GapPatternWeight 2 0 27 * 0 :=
      b4GapContribution_from_row 0 2 0 27 0 row_00_02_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_27

theorem row_00_02_00_28 : b4RowContribution (![0, 2, 2, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 30] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 30 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 908 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 30^2 = 908
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_28

theorem weighted_00_02_00_28 : b4RawGapContribution ![0, 2, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 28] = b4GapPatternWeight 2 0 28 * 0 :=
      b4GapContribution_from_row 0 2 0 28 0 row_00_02_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_28

theorem row_00_02_00_29 : b4RowContribution (![0, 2, 2, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 31] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 31 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 969 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 31^2 = 969
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_29

theorem weighted_00_02_00_29 : b4RawGapContribution ![0, 2, 0, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 29] = b4GapPatternWeight 2 0 29 * 0 :=
      b4GapContribution_from_row 0 2 0 29 0 row_00_02_00_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_29

theorem row_00_02_00_30 : b4RowContribution (![0, 2, 2, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 32] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 32 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1032 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 32^2 = 1032
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_30

theorem weighted_00_02_00_30 : b4RawGapContribution ![0, 2, 0, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 30] = b4GapPatternWeight 2 0 30 * 0 :=
      b4GapContribution_from_row 0 2 0 30 0 row_00_02_00_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_30

theorem row_00_02_00_31 : b4RowContribution (![0, 2, 2, 33] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 2, 33] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 2 + 33 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 2, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1097 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 2^2 + 33^2 = 1097
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_00_31

theorem weighted_00_02_00_31 : b4RawGapContribution ![0, 2, 0, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 0, 31] = b4GapPatternWeight 2 0 31 * 0 :=
      b4GapContribution_from_row 0 2 0 31 0 row_00_02_00_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_00_31

def dvalues_00_02_00 : Fin 32 → ℕ := ![0, 0, 0, 96, 108, 0, 0, 0, 0, 0, 0, 108, 0, 288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_00

theorem dblock_00_02_00 : b4GapPatternDBlock 0 2 0 = 600 := by
  calc
    b4GapPatternDBlock 0 2 0 = ∑ d : Fin 32, dvalues_00_02_00 d := by
      apply b4GapDBlock_of_rows 0 2 0 dvalues_00_02_00
      intro d
      fin_cases d
      · exact weighted_00_02_00_00
      · exact weighted_00_02_00_01
      · exact weighted_00_02_00_02
      · exact weighted_00_02_00_03
      · exact weighted_00_02_00_04
      · exact weighted_00_02_00_05
      · exact weighted_00_02_00_06
      · exact weighted_00_02_00_07
      · exact weighted_00_02_00_08
      · exact weighted_00_02_00_09
      · exact weighted_00_02_00_10
      · exact weighted_00_02_00_11
      · exact weighted_00_02_00_12
      · exact weighted_00_02_00_13
      · exact weighted_00_02_00_14
      · exact weighted_00_02_00_15
      · exact weighted_00_02_00_16
      · exact weighted_00_02_00_17
      · exact weighted_00_02_00_18
      · exact weighted_00_02_00_19
      · exact weighted_00_02_00_20
      · exact weighted_00_02_00_21
      · exact weighted_00_02_00_22
      · exact weighted_00_02_00_23
      · exact weighted_00_02_00_24
      · exact weighted_00_02_00_25
      · exact weighted_00_02_00_26
      · exact weighted_00_02_00_27
      · exact weighted_00_02_00_28
      · exact weighted_00_02_00_29
      · exact weighted_00_02_00_30
      · exact weighted_00_02_00_31
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_00

end Paper7MomentGapNumeric
