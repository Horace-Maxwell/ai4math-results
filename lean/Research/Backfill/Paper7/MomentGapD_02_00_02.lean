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

def layers_02_00_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 34, 37, 34, 27, 18, 10, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_00_02_00

theorem cells_02_00_02_00 : QTableValid (![2, 2, 4, 4] : Fin 4 → ℕ) layers_02_00_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_02_00

theorem valid_02_00_02_00 :
    SparseRowValid (![2, 2, 4, 4] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_00_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 4, 4] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 4 + 4 = 12
      decide
    have hzsq : (∑ i, (((![2, 2, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 40 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 4^2 + 4^2 = 40
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_02_00
#print axioms Paper7MomentGapNumeric.valid_02_00_02_00

def qvalues_02_00_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_02_00

theorem row_02_00_02_00 : b4RowContribution (![2, 2, 4, 4] : Fin 4 → ℕ) = 27 := by
  calc
    b4RowContribution (![2, 2, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_00_02_00) :=
      sparseRow_sound (![2, 2, 4, 4] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_00_02_00) valid_02_00_02_00
    _ = 27 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_02_00 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 27 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_02_00

theorem weighted_02_00_02_00 : b4RawGapContribution ![2, 0, 2, 0] = 162 := by
  calc
    b4RawGapContribution ![2, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 27 :=
      b4GapContribution_from_row 2 0 2 0 27 row_02_00_02_00
    _ = 162 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_00

theorem row_02_00_02_01 : b4RowContribution (![2, 2, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 5 = 13
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 49 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 5^2 = 49
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_01

theorem weighted_02_00_02_01 : b4RawGapContribution ![2, 0, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 0 :=
      b4GapContribution_from_row 2 0 2 1 0 row_02_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_01

theorem row_02_00_02_02 : b4RowContribution (![2, 2, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 6 = 14
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 60 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 6^2 = 60
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_02

theorem weighted_02_00_02_02 : b4RawGapContribution ![2, 0, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 0 :=
      b4GapContribution_from_row 2 0 2 2 0 row_02_00_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_02

theorem row_02_00_02_03 : b4RowContribution (![2, 2, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 7 = 15
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 7^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_03

theorem weighted_02_00_02_03 : b4RawGapContribution ![2, 0, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 0 :=
      b4GapContribution_from_row 2 0 2 3 0 row_02_00_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_03

theorem row_02_00_02_04 : b4RowContribution (![2, 2, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 8 = 16
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 88 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 8^2 = 88
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_04

theorem weighted_02_00_02_04 : b4RawGapContribution ![2, 0, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 0 :=
      b4GapContribution_from_row 2 0 2 4 0 row_02_00_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_04

theorem row_02_00_02_05 : b4RowContribution (![2, 2, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 9 = 17
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 105 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 9^2 = 105
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_05

theorem weighted_02_00_02_05 : b4RawGapContribution ![2, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 2 0 2 5 0 row_02_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_05

theorem row_02_00_02_06 : b4RowContribution (![2, 2, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 10 = 18
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 10^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_06

theorem weighted_02_00_02_06 : b4RawGapContribution ![2, 0, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 6] = b4GapPatternWeight 0 2 6 * 0 :=
      b4GapContribution_from_row 2 0 2 6 0 row_02_00_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_06

theorem row_02_00_02_07 : b4RowContribution (![2, 2, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 11] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 11 = 19
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 11^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_07

theorem weighted_02_00_02_07 : b4RawGapContribution ![2, 0, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 7] = b4GapPatternWeight 0 2 7 * 0 :=
      b4GapContribution_from_row 2 0 2 7 0 row_02_00_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_07

def layers_02_00_02_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 35, 41, 44, 45, 45, 45, 45, 45, 44, 41, 35, 27, 18, 10]]
#print axioms Paper7MomentGapNumeric.layers_02_00_02_08

theorem cells_02_00_02_08 : QTableValid (![2, 2, 4, 12] : Fin 4 → ℕ) layers_02_00_02_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_02_08

theorem valid_02_00_02_08 :
    SparseRowValid (![2, 2, 4, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_02_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 4, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 4 + 12 = 20
      decide
    have hzsq : (∑ i, (((![2, 2, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 168 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 4^2 + 12^2 = 168
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_02_08
#print axioms Paper7MomentGapNumeric.valid_02_00_02_08

def qvalues_02_00_02_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_02_08

theorem row_02_00_02_08 : b4RowContribution (![2, 2, 4, 12] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![2, 2, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_02_00_02_08) :=
      sparseRow_sound (![2, 2, 4, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_02_08) valid_02_00_02_08
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_02_08 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_02_08

theorem weighted_02_00_02_08 : b4RawGapContribution ![2, 0, 2, 8] = 540 := by
  calc
    b4RawGapContribution ![2, 0, 2, 8] = b4GapPatternWeight 0 2 8 * 45 :=
      b4GapContribution_from_row 2 0 2 8 45 row_02_00_02_08
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_08

theorem row_02_00_02_09 : b4RowContribution (![2, 2, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 13] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 13 = 21
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 13^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_09

theorem weighted_02_00_02_09 : b4RawGapContribution ![2, 0, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 9] = b4GapPatternWeight 0 2 9 * 0 :=
      b4GapContribution_from_row 2 0 2 9 0 row_02_00_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_09

def layers_02_00_02_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 35, 41, 44, 45, 45, 45, 45, 45, 45, 45, 44, 41, 35, 27]]
#print axioms Paper7MomentGapNumeric.layers_02_00_02_10

theorem cells_02_00_02_10 : QTableValid (![2, 2, 4, 14] : Fin 4 → ℕ) layers_02_00_02_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_02_10

theorem valid_02_00_02_10 :
    SparseRowValid (![2, 2, 4, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_00_02_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 4, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 4 + 14 = 22
      decide
    have hzsq : (∑ i, (((![2, 2, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 4^2 + 14^2 = 220
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_02_10
#print axioms Paper7MomentGapNumeric.valid_02_00_02_10

def qvalues_02_00_02_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_02_10

theorem row_02_00_02_10 : b4RowContribution (![2, 2, 4, 14] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![2, 2, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_02_00_02_10) :=
      sparseRow_sound (![2, 2, 4, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_00_02_10) valid_02_00_02_10
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_02_10 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_02_10

theorem weighted_02_00_02_10 : b4RawGapContribution ![2, 0, 2, 10] = 540 := by
  calc
    b4RawGapContribution ![2, 0, 2, 10] = b4GapPatternWeight 0 2 10 * 45 :=
      b4GapContribution_from_row 2 0 2 10 45 row_02_00_02_10
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_10

theorem row_02_00_02_11 : b4RowContribution (![2, 2, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 15 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 15^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_11

theorem weighted_02_00_02_11 : b4RawGapContribution ![2, 0, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 11] = b4GapPatternWeight 0 2 11 * 0 :=
      b4GapContribution_from_row 2 0 2 11 0 row_02_00_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_11

def layers_02_00_02_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 35, 41, 44, 45, 45, 45, 45, 45, 45, 45, 45, 45, 44, 41]]
#print axioms Paper7MomentGapNumeric.layers_02_00_02_12

theorem cells_02_00_02_12 : QTableValid (![2, 2, 4, 16] : Fin 4 → ℕ) layers_02_00_02_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_02_12

theorem valid_02_00_02_12 :
    SparseRowValid (![2, 2, 4, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_00_02_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 4, 16] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 4 + 16 = 24
      decide
    have hzsq : (∑ i, (((![2, 2, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 280 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 4^2 + 16^2 = 280
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_02_12
#print axioms Paper7MomentGapNumeric.valid_02_00_02_12

def qvalues_02_00_02_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_02_12

theorem row_02_00_02_12 : b4RowContribution (![2, 2, 4, 16] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![2, 2, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_02_00_02_12) :=
      sparseRow_sound (![2, 2, 4, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_00_02_12) valid_02_00_02_12
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_02_12 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_02_12

theorem weighted_02_00_02_12 : b4RawGapContribution ![2, 0, 2, 12] = 540 := by
  calc
    b4RawGapContribution ![2, 0, 2, 12] = b4GapPatternWeight 0 2 12 * 45 :=
      b4GapContribution_from_row 2 0 2 12 45 row_02_00_02_12
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_12

theorem row_02_00_02_13 : b4RowContribution (![2, 2, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 17 = 25
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 17^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_13

theorem weighted_02_00_02_13 : b4RawGapContribution ![2, 0, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 13] = b4GapPatternWeight 0 2 13 * 0 :=
      b4GapContribution_from_row 2 0 2 13 0 row_02_00_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_13

theorem row_02_00_02_14 : b4RowContribution (![2, 2, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 18 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 18^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_14

theorem weighted_02_00_02_14 : b4RawGapContribution ![2, 0, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 14] = b4GapPatternWeight 0 2 14 * 0 :=
      b4GapContribution_from_row 2 0 2 14 0 row_02_00_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_14

theorem row_02_00_02_15 : b4RowContribution (![2, 2, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 19 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 19^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_15

theorem weighted_02_00_02_15 : b4RawGapContribution ![2, 0, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 15] = b4GapPatternWeight 0 2 15 * 0 :=
      b4GapContribution_from_row 2 0 2 15 0 row_02_00_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_15

theorem row_02_00_02_16 : b4RowContribution (![2, 2, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 20 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 424 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 20^2 = 424
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_16

theorem weighted_02_00_02_16 : b4RawGapContribution ![2, 0, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 16] = b4GapPatternWeight 0 2 16 * 0 :=
      b4GapContribution_from_row 2 0 2 16 0 row_02_00_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_16

theorem row_02_00_02_17 : b4RowContribution (![2, 2, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 21 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 21^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_17

theorem weighted_02_00_02_17 : b4RawGapContribution ![2, 0, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 17] = b4GapPatternWeight 0 2 17 * 0 :=
      b4GapContribution_from_row 2 0 2 17 0 row_02_00_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_17

theorem row_02_00_02_18 : b4RowContribution (![2, 2, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 22 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 508 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 22^2 = 508
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_18

theorem weighted_02_00_02_18 : b4RawGapContribution ![2, 0, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 18] = b4GapPatternWeight 0 2 18 * 0 :=
      b4GapContribution_from_row 2 0 2 18 0 row_02_00_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_18

theorem row_02_00_02_19 : b4RowContribution (![2, 2, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 23 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 553 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 23^2 = 553
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_19

theorem weighted_02_00_02_19 : b4RawGapContribution ![2, 0, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 19] = b4GapPatternWeight 0 2 19 * 0 :=
      b4GapContribution_from_row 2 0 2 19 0 row_02_00_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_19

theorem row_02_00_02_20 : b4RowContribution (![2, 2, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 24 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 600 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 24^2 = 600
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_20

theorem weighted_02_00_02_20 : b4RawGapContribution ![2, 0, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 20] = b4GapPatternWeight 0 2 20 * 0 :=
      b4GapContribution_from_row 2 0 2 20 0 row_02_00_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_20

theorem row_02_00_02_21 : b4RowContribution (![2, 2, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 25 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 649 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 25^2 = 649
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_21

theorem weighted_02_00_02_21 : b4RawGapContribution ![2, 0, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 21] = b4GapPatternWeight 0 2 21 * 0 :=
      b4GapContribution_from_row 2 0 2 21 0 row_02_00_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_21

theorem row_02_00_02_22 : b4RowContribution (![2, 2, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 26 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 700 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 26^2 = 700
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_22

theorem weighted_02_00_02_22 : b4RawGapContribution ![2, 0, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 22] = b4GapPatternWeight 0 2 22 * 0 :=
      b4GapContribution_from_row 2 0 2 22 0 row_02_00_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_22

theorem row_02_00_02_23 : b4RowContribution (![2, 2, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 27 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 753 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 27^2 = 753
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_23

theorem weighted_02_00_02_23 : b4RawGapContribution ![2, 0, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 23] = b4GapPatternWeight 0 2 23 * 0 :=
      b4GapContribution_from_row 2 0 2 23 0 row_02_00_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_23

theorem row_02_00_02_24 : b4RowContribution (![2, 2, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 28 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 808 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 28^2 = 808
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_24

theorem weighted_02_00_02_24 : b4RawGapContribution ![2, 0, 2, 24] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 24] = b4GapPatternWeight 0 2 24 * 0 :=
      b4GapContribution_from_row 2 0 2 24 0 row_02_00_02_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_24

theorem row_02_00_02_25 : b4RowContribution (![2, 2, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 4, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 4 + 29 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 865 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 4^2 + 29^2 = 865
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_02_25

theorem weighted_02_00_02_25 : b4RawGapContribution ![2, 0, 2, 25] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 2, 25] = b4GapPatternWeight 0 2 25 * 0 :=
      b4GapContribution_from_row 2 0 2 25 0 row_02_00_02_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_02_25

def dvalues_02_00_02 : Fin 26 → ℕ := ![162, 0, 0, 0, 0, 0, 0, 0, 540, 0, 540, 0, 540, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_02

theorem dblock_02_00_02 : b4GapPatternDBlock 2 0 2 = 1782 := by
  calc
    b4GapPatternDBlock 2 0 2 = ∑ d : Fin 26, dvalues_02_00_02 d := by
      apply b4GapDBlock_of_rows 2 0 2 dvalues_02_00_02
      intro d
      fin_cases d
      · exact weighted_02_00_02_00
      · exact weighted_02_00_02_01
      · exact weighted_02_00_02_02
      · exact weighted_02_00_02_03
      · exact weighted_02_00_02_04
      · exact weighted_02_00_02_05
      · exact weighted_02_00_02_06
      · exact weighted_02_00_02_07
      · exact weighted_02_00_02_08
      · exact weighted_02_00_02_09
      · exact weighted_02_00_02_10
      · exact weighted_02_00_02_11
      · exact weighted_02_00_02_12
      · exact weighted_02_00_02_13
      · exact weighted_02_00_02_14
      · exact weighted_02_00_02_15
      · exact weighted_02_00_02_16
      · exact weighted_02_00_02_17
      · exact weighted_02_00_02_18
      · exact weighted_02_00_02_19
      · exact weighted_02_00_02_20
      · exact weighted_02_00_02_21
      · exact weighted_02_00_02_22
      · exact weighted_02_00_02_23
      · exact weighted_02_00_02_24
      · exact weighted_02_00_02_25
    _ = 1782 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_02

end Paper7MomentGapNumeric
