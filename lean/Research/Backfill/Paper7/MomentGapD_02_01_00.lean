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

def layers_02_01_00_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 10, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 28, 34, 34, 28, 19, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_01_00_00

theorem cells_02_01_00_00 : QTableValid (![2, 3, 3, 3] : Fin 4 → ℕ) layers_02_01_00_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_00_00

theorem valid_02_01_00_00 :
    SparseRowValid (![2, 3, 3, 3] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_01_00_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 3, 3] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 3 + 3 = 11
      decide
    have hzsq : (∑ i, (((![2, 3, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 31 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 3^2 + 3^2 = 31
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_00_00
#print axioms Paper7MomentGapNumeric.valid_02_01_00_00

def qvalues_02_01_00_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_00_00

theorem row_02_01_00_00 : b4RowContribution (![2, 3, 3, 3] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![2, 3, 3, 3] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_02_01_00_00) :=
      sparseRow_sound (![2, 3, 3, 3] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_01_00_00) valid_02_01_00_00
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_00_00 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_00_00

theorem weighted_02_01_00_00 : b4RawGapContribution ![2, 1, 0, 0] = 16 := by
  calc
    b4RawGapContribution ![2, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 4 :=
      b4GapContribution_from_row 2 1 0 0 4 row_02_01_00_00
    _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_00

def layers_02_01_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 10, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 29, 37, 40, 37, 29, 19, 10, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_02_01_00_01

theorem cells_02_01_00_01 : QTableValid (![2, 3, 3, 4] : Fin 4 → ℕ) layers_02_01_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_00_01

theorem valid_02_01_00_01 :
    SparseRowValid (![2, 3, 3, 4] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_01_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 3, 4] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 3 + 4 = 12
      decide
    have hzsq : (∑ i, (((![2, 3, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 38 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 3^2 + 4^2 = 38
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_00_01
#print axioms Paper7MomentGapNumeric.valid_02_01_00_01

def qvalues_02_01_00_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_00_01

theorem row_02_01_00_01 : b4RowContribution (![2, 3, 3, 4] : Fin 4 → ℕ) = 37 := by
  calc
    b4RowContribution (![2, 3, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_02_01_00_01) :=
      sparseRow_sound (![2, 3, 3, 4] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_01_00_01) valid_02_01_00_01
    _ = 37 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_00_01 Q := by
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
        _ = 37 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_00_01

theorem weighted_02_01_00_01 : b4RawGapContribution ![2, 1, 0, 1] = 444 := by
  calc
    b4RawGapContribution ![2, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 37 :=
      b4GapContribution_from_row 2 1 0 1 37 row_02_01_00_01
    _ = 444 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_01

theorem row_02_01_00_02 : b4RowContribution (![2, 3, 3, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 5 = 13
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 47 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 5^2 = 47
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_02

theorem weighted_02_01_00_02 : b4RawGapContribution ![2, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 2 1 0 2 0 row_02_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_02

theorem row_02_01_00_03 : b4RowContribution (![2, 3, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 6 = 14
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 6^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_03

theorem weighted_02_01_00_03 : b4RawGapContribution ![2, 1, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 0 :=
      b4GapContribution_from_row 2 1 0 3 0 row_02_01_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_03

theorem row_02_01_00_04 : b4RowContribution (![2, 3, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 7 = 15
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 71 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 7^2 = 71
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_04

theorem weighted_02_01_00_04 : b4RawGapContribution ![2, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 2 1 0 4 0 row_02_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_04

theorem row_02_01_00_05 : b4RowContribution (![2, 3, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 8 = 16
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 86 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 8^2 = 86
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_05

theorem weighted_02_01_00_05 : b4RawGapContribution ![2, 1, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 0 :=
      b4GapContribution_from_row 2 1 0 5 0 row_02_01_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_05

theorem row_02_01_00_06 : b4RowContribution (![2, 3, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 9 = 17
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 103 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 9^2 = 103
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_06

theorem weighted_02_01_00_06 : b4RawGapContribution ![2, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 2 1 0 6 0 row_02_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_06

theorem row_02_01_00_07 : b4RowContribution (![2, 3, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 10 = 18
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 10^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_07

theorem weighted_02_01_00_07 : b4RawGapContribution ![2, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 2 1 0 7 0 row_02_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_07

theorem row_02_01_00_08 : b4RowContribution (![2, 3, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 11] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 11 = 19
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 143 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 11^2 = 143
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_08

theorem weighted_02_01_00_08 : b4RawGapContribution ![2, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 2 1 0 8 0 row_02_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_08

def layers_02_01_00_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 10, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 29, 38, 44, 47, 48, 48, 48, 48, 48, 47, 44, 38, 29, 19, 10]]
#print axioms Paper7MomentGapNumeric.layers_02_01_00_09

theorem cells_02_01_00_09 : QTableValid (![2, 3, 3, 12] : Fin 4 → ℕ) layers_02_01_00_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_00_09

theorem valid_02_01_00_09 :
    SparseRowValid (![2, 3, 3, 12] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_01_00_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 3, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 3 + 12 = 20
      decide
    have hzsq : (∑ i, (((![2, 3, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 3^2 + 12^2 = 166
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_00_09
#print axioms Paper7MomentGapNumeric.valid_02_01_00_09

def qvalues_02_01_00_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_00_09

theorem row_02_01_00_09 : b4RowContribution (![2, 3, 3, 12] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![2, 3, 3, 12] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_02_01_00_09) :=
      sparseRow_sound (![2, 3, 3, 12] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_01_00_09) valid_02_01_00_09
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_00_09 Q := by
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
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_00_09

theorem weighted_02_01_00_09 : b4RawGapContribution ![2, 1, 0, 9] = 564 := by
  calc
    b4RawGapContribution ![2, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 47 :=
      b4GapContribution_from_row 2 1 0 9 47 row_02_01_00_09
    _ = 564 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_09

theorem row_02_01_00_10 : b4RowContribution (![2, 3, 3, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 13] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 13 = 21
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 191 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 13^2 = 191
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_10

theorem weighted_02_01_00_10 : b4RawGapContribution ![2, 1, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 0 :=
      b4GapContribution_from_row 2 1 0 10 0 row_02_01_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_10

def layers_02_01_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 10, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 29, 38, 44, 47, 48, 48, 48, 48, 48, 48, 48, 47, 44, 38, 29]]
#print axioms Paper7MomentGapNumeric.layers_02_01_00_11

theorem cells_02_01_00_11 : QTableValid (![2, 3, 3, 14] : Fin 4 → ℕ) layers_02_01_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_00_11

theorem valid_02_01_00_11 :
    SparseRowValid (![2, 3, 3, 14] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_02_01_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 3, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 3 + 14 = 22
      decide
    have hzsq : (∑ i, (((![2, 3, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 3^2 + 14^2 = 218
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_00_11
#print axioms Paper7MomentGapNumeric.valid_02_01_00_11

def qvalues_02_01_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_00_11

theorem row_02_01_00_11 : b4RowContribution (![2, 3, 3, 14] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![2, 3, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_02_01_00_11) :=
      sparseRow_sound (![2, 3, 3, 14] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_02_01_00_11) valid_02_01_00_11
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_00_11 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_00_11

theorem weighted_02_01_00_11 : b4RawGapContribution ![2, 1, 0, 11] = 576 := by
  calc
    b4RawGapContribution ![2, 1, 0, 11] = b4GapPatternWeight 1 0 11 * 48 :=
      b4GapContribution_from_row 2 1 0 11 48 row_02_01_00_11
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_11

theorem row_02_01_00_12 : b4RowContribution (![2, 3, 3, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 15 = 23
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 15^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_12

theorem weighted_02_01_00_12 : b4RawGapContribution ![2, 1, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 12] = b4GapPatternWeight 1 0 12 * 0 :=
      b4GapContribution_from_row 2 1 0 12 0 row_02_01_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_12

def layers_02_01_00_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 10, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 29, 38, 44, 47, 48, 48, 48, 48, 48, 48, 48, 48, 48, 47, 44]]
#print axioms Paper7MomentGapNumeric.layers_02_01_00_13

theorem cells_02_01_00_13 : QTableValid (![2, 3, 3, 16] : Fin 4 → ℕ) layers_02_01_00_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_00_13

theorem valid_02_01_00_13 :
    SparseRowValid (![2, 3, 3, 16] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_00_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 3, 16] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 3 + 16 = 24
      decide
    have hzsq : (∑ i, (((![2, 3, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 3^2 + 16^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_00_13
#print axioms Paper7MomentGapNumeric.valid_02_01_00_13

def qvalues_02_01_00_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_00_13

theorem row_02_01_00_13 : b4RowContribution (![2, 3, 3, 16] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![2, 3, 3, 16] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_02_01_00_13) :=
      sparseRow_sound (![2, 3, 3, 16] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_00_13) valid_02_01_00_13
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_00_13 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_00_13

theorem weighted_02_01_00_13 : b4RawGapContribution ![2, 1, 0, 13] = 576 := by
  calc
    b4RawGapContribution ![2, 1, 0, 13] = b4GapPatternWeight 1 0 13 * 48 :=
      b4GapContribution_from_row 2 1 0 13 48 row_02_01_00_13
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_13

theorem row_02_01_00_14 : b4RowContribution (![2, 3, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 17 = 25
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 17^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_14

theorem weighted_02_01_00_14 : b4RawGapContribution ![2, 1, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 14] = b4GapPatternWeight 1 0 14 * 0 :=
      b4GapContribution_from_row 2 1 0 14 0 row_02_01_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_14

theorem row_02_01_00_15 : b4RowContribution (![2, 3, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 18 = 26
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 18^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_15

theorem weighted_02_01_00_15 : b4RawGapContribution ![2, 1, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 15] = b4GapPatternWeight 1 0 15 * 0 :=
      b4GapContribution_from_row 2 1 0 15 0 row_02_01_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_15

theorem row_02_01_00_16 : b4RowContribution (![2, 3, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 19 = 27
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 19^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_16

theorem weighted_02_01_00_16 : b4RawGapContribution ![2, 1, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 16] = b4GapPatternWeight 1 0 16 * 0 :=
      b4GapContribution_from_row 2 1 0 16 0 row_02_01_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_16

theorem row_02_01_00_17 : b4RowContribution (![2, 3, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 20 = 28
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 20^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_17

theorem weighted_02_01_00_17 : b4RawGapContribution ![2, 1, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 17] = b4GapPatternWeight 1 0 17 * 0 :=
      b4GapContribution_from_row 2 1 0 17 0 row_02_01_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_17

theorem row_02_01_00_18 : b4RowContribution (![2, 3, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 21 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 21^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_18

theorem weighted_02_01_00_18 : b4RawGapContribution ![2, 1, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 18] = b4GapPatternWeight 1 0 18 * 0 :=
      b4GapContribution_from_row 2 1 0 18 0 row_02_01_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_18

theorem row_02_01_00_19 : b4RowContribution (![2, 3, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 22 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 22^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_19

theorem weighted_02_01_00_19 : b4RawGapContribution ![2, 1, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 19] = b4GapPatternWeight 1 0 19 * 0 :=
      b4GapContribution_from_row 2 1 0 19 0 row_02_01_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_19

theorem row_02_01_00_20 : b4RowContribution (![2, 3, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 23 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 551 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 23^2 = 551
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_20

theorem weighted_02_01_00_20 : b4RawGapContribution ![2, 1, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 20] = b4GapPatternWeight 1 0 20 * 0 :=
      b4GapContribution_from_row 2 1 0 20 0 row_02_01_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_20

theorem row_02_01_00_21 : b4RowContribution (![2, 3, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 24 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 598 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 24^2 = 598
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_21

theorem weighted_02_01_00_21 : b4RawGapContribution ![2, 1, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 21] = b4GapPatternWeight 1 0 21 * 0 :=
      b4GapContribution_from_row 2 1 0 21 0 row_02_01_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_21

theorem row_02_01_00_22 : b4RowContribution (![2, 3, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 25 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 647 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 25^2 = 647
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_22

theorem weighted_02_01_00_22 : b4RawGapContribution ![2, 1, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 22] = b4GapPatternWeight 1 0 22 * 0 :=
      b4GapContribution_from_row 2 1 0 22 0 row_02_01_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_22

theorem row_02_01_00_23 : b4RowContribution (![2, 3, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 26 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 698 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 26^2 = 698
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_23

theorem weighted_02_01_00_23 : b4RawGapContribution ![2, 1, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 23] = b4GapPatternWeight 1 0 23 * 0 :=
      b4GapContribution_from_row 2 1 0 23 0 row_02_01_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_23

theorem row_02_01_00_24 : b4RowContribution (![2, 3, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 27 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 751 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 27^2 = 751
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_24

theorem weighted_02_01_00_24 : b4RawGapContribution ![2, 1, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 24] = b4GapPatternWeight 1 0 24 * 0 :=
      b4GapContribution_from_row 2 1 0 24 0 row_02_01_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_24

theorem row_02_01_00_25 : b4RowContribution (![2, 3, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 28 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 806 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 28^2 = 806
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_25

theorem weighted_02_01_00_25 : b4RawGapContribution ![2, 1, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 25] = b4GapPatternWeight 1 0 25 * 0 :=
      b4GapContribution_from_row 2 1 0 25 0 row_02_01_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_25

theorem row_02_01_00_26 : b4RowContribution (![2, 3, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 3, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 3 + 29 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 863 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 3^2 + 29^2 = 863
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_00_26

theorem weighted_02_01_00_26 : b4RawGapContribution ![2, 1, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 0, 26] = b4GapPatternWeight 1 0 26 * 0 :=
      b4GapContribution_from_row 2 1 0 26 0 row_02_01_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_00_26

def dvalues_02_01_00 : Fin 27 → ℕ := ![16, 444, 0, 0, 0, 0, 0, 0, 0, 564, 0, 576, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_00

theorem dblock_02_01_00 : b4GapPatternDBlock 2 1 0 = 2176 := by
  calc
    b4GapPatternDBlock 2 1 0 = ∑ d : Fin 27, dvalues_02_01_00 d := by
      apply b4GapDBlock_of_rows 2 1 0 dvalues_02_01_00
      intro d
      fin_cases d
      · exact weighted_02_01_00_00
      · exact weighted_02_01_00_01
      · exact weighted_02_01_00_02
      · exact weighted_02_01_00_03
      · exact weighted_02_01_00_04
      · exact weighted_02_01_00_05
      · exact weighted_02_01_00_06
      · exact weighted_02_01_00_07
      · exact weighted_02_01_00_08
      · exact weighted_02_01_00_09
      · exact weighted_02_01_00_10
      · exact weighted_02_01_00_11
      · exact weighted_02_01_00_12
      · exact weighted_02_01_00_13
      · exact weighted_02_01_00_14
      · exact weighted_02_01_00_15
      · exact weighted_02_01_00_16
      · exact weighted_02_01_00_17
      · exact weighted_02_01_00_18
      · exact weighted_02_01_00_19
      · exact weighted_02_01_00_20
      · exact weighted_02_01_00_21
      · exact weighted_02_01_00_22
      · exact weighted_02_01_00_23
      · exact weighted_02_01_00_24
      · exact weighted_02_01_00_25
      · exact weighted_02_01_00_26
    _ = 2176 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_00

end Paper7MomentGapNumeric
