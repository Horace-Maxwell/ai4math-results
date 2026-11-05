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

def layers_03_00_00_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 31, 40, 44, 40, 31, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_03_00_00_00

theorem cells_03_00_00_00 : QTableValid (![3, 3, 3, 3] : Fin 4 → ℕ) layers_03_00_00_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_00_00

theorem valid_03_00_00_00 :
    SparseRowValid (![3, 3, 3, 3] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_00_00_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 3, 3] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 3 + 3 = 12
      decide
    have hzsq : (∑ i, (((![3, 3, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 36 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 3^2 + 3^2 = 36
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_00_00
#print axioms Paper7MomentGapNumeric.valid_03_00_00_00

def qvalues_03_00_00_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_00_00

theorem row_03_00_00_00 : b4RowContribution (![3, 3, 3, 3] : Fin 4 → ℕ) = 44 := by
  calc
    b4RowContribution (![3, 3, 3, 3] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_03_00_00_00) :=
      sparseRow_sound (![3, 3, 3, 3] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_00_00_00) valid_03_00_00_00
    _ = 44 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_00_00 Q := by
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
        _ = 44 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_00_00

theorem weighted_03_00_00_00 : b4RawGapContribution ![3, 0, 0, 0] = 44 := by
  calc
    b4RawGapContribution ![3, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 44 :=
      b4GapContribution_from_row 3 0 0 0 44 row_03_00_00_00
    _ = 44 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_00

def layers_03_00_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 32, 43, 50, 50, 43, 32, 20, 10, 4, 1, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_03_00_00_01

theorem cells_03_00_00_01 : QTableValid (![3, 3, 3, 4] : Fin 4 → ℕ) layers_03_00_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_00_01

theorem valid_03_00_00_01 :
    SparseRowValid (![3, 3, 3, 4] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_00_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 3, 4] : Fin 4 → ℕ) i) = 13 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 3 + 4 = 13
      decide
    have hzsq : (∑ i, (((![3, 3, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 43 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 3^2 + 4^2 = 43
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_00_01
#print axioms Paper7MomentGapNumeric.valid_03_00_00_01

def qvalues_03_00_00_01 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_00_01

theorem row_03_00_00_01 : b4RowContribution (![3, 3, 3, 4] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![3, 3, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_03_00_00_01) :=
      sparseRow_sound (![3, 3, 3, 4] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_00_00_01) valid_03_00_00_01
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_00_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_00_01

theorem weighted_03_00_00_01 : b4RawGapContribution ![3, 0, 0, 1] = 16 := by
  calc
    b4RawGapContribution ![3, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 4 :=
      b4GapContribution_from_row 3 0 0 1 4 row_03_00_00_01
    _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_01

theorem row_03_00_00_02 : b4RowContribution (![3, 3, 3, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 5] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 5 = 14
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 52 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 5^2 = 52
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_02

theorem weighted_03_00_00_02 : b4RawGapContribution ![3, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 3 0 0 2 0 row_03_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_02

theorem row_03_00_00_03 : b4RowContribution (![3, 3, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 6 = 15
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 63 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 6^2 = 63
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_03

theorem weighted_03_00_00_03 : b4RawGapContribution ![3, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 3 0 0 3 0 row_03_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_03

theorem row_03_00_00_04 : b4RowContribution (![3, 3, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 7 = 16
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 76 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 7^2 = 76
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_04

theorem weighted_03_00_00_04 : b4RawGapContribution ![3, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 3 0 0 4 0 row_03_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_04

theorem row_03_00_00_05 : b4RowContribution (![3, 3, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 8 = 17
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 91 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 8^2 = 91
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_05

theorem weighted_03_00_00_05 : b4RawGapContribution ![3, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 3 0 0 5 0 row_03_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_05

theorem row_03_00_00_06 : b4RowContribution (![3, 3, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 9 = 18
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 9^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_06

theorem weighted_03_00_00_06 : b4RawGapContribution ![3, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 3 0 0 6 0 row_03_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_06

theorem row_03_00_00_07 : b4RowContribution (![3, 3, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 10 = 19
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 127 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 10^2 = 127
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_07

theorem weighted_03_00_00_07 : b4RawGapContribution ![3, 0, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 0 :=
      b4GapContribution_from_row 3 0 0 7 0 row_03_00_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_07

theorem row_03_00_00_08 : b4RowContribution (![3, 3, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 11] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 11 = 20
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 11^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_08

theorem weighted_03_00_00_08 : b4RawGapContribution ![3, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 3 0 0 8 0 row_03_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_08

theorem row_03_00_00_09 : b4RowContribution (![3, 3, 3, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 12 = 21
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 12^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_09

theorem weighted_03_00_00_09 : b4RawGapContribution ![3, 0, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 0 :=
      b4GapContribution_from_row 3 0 0 9 0 row_03_00_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_09

theorem row_03_00_00_10 : b4RowContribution (![3, 3, 3, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 13 = 22
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 13^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_10

theorem weighted_03_00_00_10 : b4RawGapContribution ![3, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 3 0 0 10 0 row_03_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_10

def layers_03_00_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 32, 44, 54, 60, 63, 64, 64, 64, 64, 64, 64, 63, 60, 54, 44]]
#print axioms Paper7MomentGapNumeric.layers_03_00_00_11

theorem cells_03_00_00_11 : QTableValid (![3, 3, 3, 14] : Fin 4 → ℕ) layers_03_00_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_00_11

theorem valid_03_00_00_11 :
    SparseRowValid (![3, 3, 3, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_03_00_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 3, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 3 + 14 = 23
      decide
    have hzsq : (∑ i, (((![3, 3, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 223 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 3^2 + 14^2 = 223
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_00_11
#print axioms Paper7MomentGapNumeric.valid_03_00_00_11

def qvalues_03_00_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_00_11

theorem row_03_00_00_11 : b4RowContribution (![3, 3, 3, 14] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![3, 3, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_03_00_00_11) :=
      sparseRow_sound (![3, 3, 3, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_03_00_00_11) valid_03_00_00_11
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_00_11 Q := by
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_00_11

theorem weighted_03_00_00_11 : b4RawGapContribution ![3, 0, 0, 11] = 256 := by
  calc
    b4RawGapContribution ![3, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 64 :=
      b4GapContribution_from_row 3 0 0 11 64 row_03_00_00_11
    _ = 256 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_11

theorem row_03_00_00_12 : b4RowContribution (![3, 3, 3, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 15 = 24
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 15^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_12

theorem weighted_03_00_00_12 : b4RawGapContribution ![3, 0, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 0 :=
      b4GapContribution_from_row 3 0 0 12 0 row_03_00_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_12

def layers_03_00_00_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 32, 44, 54, 60, 63, 64, 64, 64, 64, 64, 64, 64, 64, 63, 60]]
#print axioms Paper7MomentGapNumeric.layers_03_00_00_13

theorem cells_03_00_00_13 : QTableValid (![3, 3, 3, 16] : Fin 4 → ℕ) layers_03_00_00_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_00_13

theorem valid_03_00_00_13 :
    SparseRowValid (![3, 3, 3, 16] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_00_00_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 3, 16] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 3 + 16 = 25
      decide
    have hzsq : (∑ i, (((![3, 3, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 3^2 + 16^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_00_13
#print axioms Paper7MomentGapNumeric.valid_03_00_00_13

def qvalues_03_00_00_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_00_13

theorem row_03_00_00_13 : b4RowContribution (![3, 3, 3, 16] : Fin 4 → ℕ) = 60 := by
  calc
    b4RowContribution (![3, 3, 3, 16] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_03_00_00_13) :=
      sparseRow_sound (![3, 3, 3, 16] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_00_00_13) valid_03_00_00_13
    _ = 60 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_00_13 Q := by
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
        _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_00_13

theorem weighted_03_00_00_13 : b4RawGapContribution ![3, 0, 0, 13] = 240 := by
  calc
    b4RawGapContribution ![3, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 60 :=
      b4GapContribution_from_row 3 0 0 13 60 row_03_00_00_13
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_13

theorem row_03_00_00_14 : b4RowContribution (![3, 3, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 17 = 26
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 17^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_14

theorem weighted_03_00_00_14 : b4RawGapContribution ![3, 0, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 14] = b4GapPatternWeight 0 0 14 * 0 :=
      b4GapContribution_from_row 3 0 0 14 0 row_03_00_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_14

theorem row_03_00_00_15 : b4RowContribution (![3, 3, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 18 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 18^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_15

theorem weighted_03_00_00_15 : b4RawGapContribution ![3, 0, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 15] = b4GapPatternWeight 0 0 15 * 0 :=
      b4GapContribution_from_row 3 0 0 15 0 row_03_00_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_15

theorem row_03_00_00_16 : b4RowContribution (![3, 3, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 19 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 19^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_16

theorem weighted_03_00_00_16 : b4RawGapContribution ![3, 0, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 16] = b4GapPatternWeight 0 0 16 * 0 :=
      b4GapContribution_from_row 3 0 0 16 0 row_03_00_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_16

theorem row_03_00_00_17 : b4RowContribution (![3, 3, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 20 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 20^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_17

theorem weighted_03_00_00_17 : b4RawGapContribution ![3, 0, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 17] = b4GapPatternWeight 0 0 17 * 0 :=
      b4GapContribution_from_row 3 0 0 17 0 row_03_00_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_17

theorem row_03_00_00_18 : b4RowContribution (![3, 3, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 21 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 21^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_18

theorem weighted_03_00_00_18 : b4RawGapContribution ![3, 0, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 18] = b4GapPatternWeight 0 0 18 * 0 :=
      b4GapContribution_from_row 3 0 0 18 0 row_03_00_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_18

theorem row_03_00_00_19 : b4RowContribution (![3, 3, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 22 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 511 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 22^2 = 511
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_19

theorem weighted_03_00_00_19 : b4RawGapContribution ![3, 0, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 19] = b4GapPatternWeight 0 0 19 * 0 :=
      b4GapContribution_from_row 3 0 0 19 0 row_03_00_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_19

theorem row_03_00_00_20 : b4RowContribution (![3, 3, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 23 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 556 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 23^2 = 556
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_20

theorem weighted_03_00_00_20 : b4RawGapContribution ![3, 0, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 20] = b4GapPatternWeight 0 0 20 * 0 :=
      b4GapContribution_from_row 3 0 0 20 0 row_03_00_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_20

theorem row_03_00_00_21 : b4RowContribution (![3, 3, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 24 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 603 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 24^2 = 603
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_21

theorem weighted_03_00_00_21 : b4RawGapContribution ![3, 0, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 21] = b4GapPatternWeight 0 0 21 * 0 :=
      b4GapContribution_from_row 3 0 0 21 0 row_03_00_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_21

theorem row_03_00_00_22 : b4RowContribution (![3, 3, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 25 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 652 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 25^2 = 652
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_22

theorem weighted_03_00_00_22 : b4RawGapContribution ![3, 0, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 22] = b4GapPatternWeight 0 0 22 * 0 :=
      b4GapContribution_from_row 3 0 0 22 0 row_03_00_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_22

theorem row_03_00_00_23 : b4RowContribution (![3, 3, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 26 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 703 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 26^2 = 703
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_23

theorem weighted_03_00_00_23 : b4RawGapContribution ![3, 0, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 23] = b4GapPatternWeight 0 0 23 * 0 :=
      b4GapContribution_from_row 3 0 0 23 0 row_03_00_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_23

theorem row_03_00_00_24 : b4RowContribution (![3, 3, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 27 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 756 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 27^2 = 756
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_24

theorem weighted_03_00_00_24 : b4RawGapContribution ![3, 0, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 24] = b4GapPatternWeight 0 0 24 * 0 :=
      b4GapContribution_from_row 3 0 0 24 0 row_03_00_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_24

theorem row_03_00_00_25 : b4RowContribution (![3, 3, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 3, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 3 + 28 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 811 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 3^2 + 28^2 = 811
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_00_25

theorem weighted_03_00_00_25 : b4RawGapContribution ![3, 0, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 0, 25] = b4GapPatternWeight 0 0 25 * 0 :=
      b4GapContribution_from_row 3 0 0 25 0 row_03_00_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_00_25

def dvalues_03_00_00 : Fin 26 → ℕ := ![44, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_00

theorem dblock_03_00_00 : b4GapPatternDBlock 3 0 0 = 556 := by
  calc
    b4GapPatternDBlock 3 0 0 = ∑ d : Fin 26, dvalues_03_00_00 d := by
      apply b4GapDBlock_of_rows 3 0 0 dvalues_03_00_00
      intro d
      fin_cases d
      · exact weighted_03_00_00_00
      · exact weighted_03_00_00_01
      · exact weighted_03_00_00_02
      · exact weighted_03_00_00_03
      · exact weighted_03_00_00_04
      · exact weighted_03_00_00_05
      · exact weighted_03_00_00_06
      · exact weighted_03_00_00_07
      · exact weighted_03_00_00_08
      · exact weighted_03_00_00_09
      · exact weighted_03_00_00_10
      · exact weighted_03_00_00_11
      · exact weighted_03_00_00_12
      · exact weighted_03_00_00_13
      · exact weighted_03_00_00_14
      · exact weighted_03_00_00_15
      · exact weighted_03_00_00_16
      · exact weighted_03_00_00_17
      · exact weighted_03_00_00_18
      · exact weighted_03_00_00_19
      · exact weighted_03_00_00_20
      · exact weighted_03_00_00_21
      · exact weighted_03_00_00_22
      · exact weighted_03_00_00_23
      · exact weighted_03_00_00_24
      · exact weighted_03_00_00_25
    _ = 556 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_00

end Paper7MomentGapNumeric
