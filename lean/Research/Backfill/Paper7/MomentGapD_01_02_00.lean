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

theorem row_01_02_00_00 : b4RowContribution (![1, 3, 3, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 3] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 3 = 10
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 28 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 3^2 = 28
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_00

theorem weighted_01_02_00_00 : b4RawGapContribution ![1, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 1 2 0 0 0 row_01_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_00

def layers_01_02_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 27, 27, 23, 16, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_01

theorem cells_01_02_00_01 : QTableValid (![1, 3, 3, 4] : Fin 4 → ℕ) layers_01_02_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_01

theorem valid_01_02_00_01 :
    SparseRowValid (![1, 3, 3, 4] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 4] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 4 = 11
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 35 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 4^2 = 35
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_01
#print axioms Paper7MomentGapNumeric.valid_01_02_00_01

def qvalues_01_02_00_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_01

theorem row_01_02_00_01 : b4RowContribution (![1, 3, 3, 4] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 3, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_02_00_01) :=
      sparseRow_sound (![1, 3, 3, 4] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_00_01) valid_01_02_00_01
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_01 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_00_01

theorem weighted_01_02_00_01 : b4RawGapContribution ![1, 2, 0, 1] = 192 := by
  calc
    b4RawGapContribution ![1, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 16 :=
      b4GapContribution_from_row 1 2 0 1 16 row_01_02_00_01
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_01

def layers_01_02_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 30, 28, 23, 16, 9, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_02

theorem cells_01_02_00_02 : QTableValid (![1, 3, 3, 5] : Fin 4 → ℕ) layers_01_02_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_02

theorem valid_01_02_00_02 :
    SparseRowValid (![1, 3, 3, 5] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 5] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 5 = 12
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 44 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 5^2 = 44
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_02
#print axioms Paper7MomentGapNumeric.valid_01_02_00_02

def qvalues_01_02_00_02 : Fin 19 → ℕ := ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_02

theorem row_01_02_00_02 : b4RowContribution (![1, 3, 3, 5] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![1, 3, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_02) :=
      sparseRow_sound (![1, 3, 3, 5] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_02) valid_01_02_00_02
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_02_00_02

theorem weighted_01_02_00_02 : b4RawGapContribution ![1, 2, 0, 2] = 108 := by
  calc
    b4RawGapContribution ![1, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 9 :=
      b4GapContribution_from_row 1 2 0 2 9 row_01_02_00_02
    _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_02

theorem row_01_02_00_03 : b4RowContribution (![1, 3, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 6 = 13
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 55 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 6^2 = 55
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_03

theorem weighted_01_02_00_03 : b4RawGapContribution ![1, 2, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 0 :=
      b4GapContribution_from_row 1 2 0 3 0 row_01_02_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_03

theorem row_01_02_00_04 : b4RowContribution (![1, 3, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 7 = 14
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 68 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 7^2 = 68
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_04

theorem weighted_01_02_00_04 : b4RawGapContribution ![1, 2, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 0 :=
      b4GapContribution_from_row 1 2 0 4 0 row_01_02_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_04

theorem row_01_02_00_05 : b4RowContribution (![1, 3, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 8 = 15
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 83 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 8^2 = 83
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_05

theorem weighted_01_02_00_05 : b4RawGapContribution ![1, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 1 2 0 5 0 row_01_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_05

theorem row_01_02_00_06 : b4RowContribution (![1, 3, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 9 = 16
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 9^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_06

theorem weighted_01_02_00_06 : b4RawGapContribution ![1, 2, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 0 :=
      b4GapContribution_from_row 1 2 0 6 0 row_01_02_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_06

theorem row_01_02_00_07 : b4RowContribution (![1, 3, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 10 = 17
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 119 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 10^2 = 119
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_07

theorem weighted_01_02_00_07 : b4RawGapContribution ![1, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 1 2 0 7 0 row_01_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_07

theorem row_01_02_00_08 : b4RowContribution (![1, 3, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 11 = 18
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 140 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 11^2 = 140
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_08

theorem weighted_01_02_00_08 : b4RawGapContribution ![1, 2, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 8] = b4GapPatternWeight 2 0 8 * 0 :=
      b4GapContribution_from_row 1 2 0 8 0 row_01_02_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_08

def layers_01_02_00_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 31, 32, 32, 32, 32, 32, 32, 31, 28, 23, 16, 9, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_09

theorem cells_01_02_00_09 : QTableValid (![1, 3, 3, 12] : Fin 4 → ℕ) layers_01_02_00_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_09

theorem valid_01_02_00_09 :
    SparseRowValid (![1, 3, 3, 12] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_01_02_00_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 12 = 19
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 12^2 = 163
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_09
#print axioms Paper7MomentGapNumeric.valid_01_02_00_09

def qvalues_01_02_00_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_09

theorem row_01_02_00_09 : b4RowContribution (![1, 3, 3, 12] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 3, 3, 12] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_01_02_00_09) :=
      sparseRow_sound (![1, 3, 3, 12] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_01_02_00_09) valid_01_02_00_09
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_09 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_00_09

theorem weighted_01_02_00_09 : b4RawGapContribution ![1, 2, 0, 9] = 192 := by
  calc
    b4RawGapContribution ![1, 2, 0, 9] = b4GapPatternWeight 2 0 9 * 16 :=
      b4GapContribution_from_row 1 2 0 9 16 row_01_02_00_09
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_09

def layers_01_02_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 31, 32, 32, 32, 32, 32, 32, 32, 31, 28, 23, 16, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_10

theorem cells_01_02_00_10 : QTableValid (![1, 3, 3, 13] : Fin 4 → ℕ) layers_01_02_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_10

theorem valid_01_02_00_10 :
    SparseRowValid (![1, 3, 3, 13] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 13] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 13 = 20
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 13^2 = 188
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_10
#print axioms Paper7MomentGapNumeric.valid_01_02_00_10

def qvalues_01_02_00_10 : Fin 19 → ℕ := ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_10

theorem row_01_02_00_10 : b4RowContribution (![1, 3, 3, 13] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![1, 3, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_10) :=
      sparseRow_sound (![1, 3, 3, 13] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_02_00_10) valid_01_02_00_10
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_10 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_02_00_10

theorem weighted_01_02_00_10 : b4RawGapContribution ![1, 2, 0, 10] = 108 := by
  calc
    b4RawGapContribution ![1, 2, 0, 10] = b4GapPatternWeight 2 0 10 * 9 :=
      b4GapContribution_from_row 1 2 0 10 9 row_01_02_00_10
    _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_10

def layers_01_02_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 31, 32, 32, 32, 32, 32, 32, 32, 32, 31, 28, 23, 16]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_11

theorem cells_01_02_00_11 : QTableValid (![1, 3, 3, 14] : Fin 4 → ℕ) layers_01_02_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_11

theorem valid_01_02_00_11 :
    SparseRowValid (![1, 3, 3, 14] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_01_02_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 14 = 21
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 14^2 = 215
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_11
#print axioms Paper7MomentGapNumeric.valid_01_02_00_11

def qvalues_01_02_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_11

theorem row_01_02_00_11 : b4RowContribution (![1, 3, 3, 14] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 3, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_01_02_00_11) :=
      sparseRow_sound (![1, 3, 3, 14] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_01_02_00_11) valid_01_02_00_11
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_11 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_00_11

theorem weighted_01_02_00_11 : b4RawGapContribution ![1, 2, 0, 11] = 384 := by
  calc
    b4RawGapContribution ![1, 2, 0, 11] = b4GapPatternWeight 2 0 11 * 32 :=
      b4GapContribution_from_row 1 2 0 11 32 row_01_02_00_11
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_11

def layers_01_02_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 31, 28, 23]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_12

theorem cells_01_02_00_12 : QTableValid (![1, 3, 3, 15] : Fin 4 → ℕ) layers_01_02_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_12

theorem valid_01_02_00_12 :
    SparseRowValid (![1, 3, 3, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_02_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 15] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 15 = 22
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 15^2 = 244
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_12
#print axioms Paper7MomentGapNumeric.valid_01_02_00_12

def qvalues_01_02_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_12

theorem row_01_02_00_12 : b4RowContribution (![1, 3, 3, 15] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 3, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_02_00_12) :=
      sparseRow_sound (![1, 3, 3, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_02_00_12) valid_01_02_00_12
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_12 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_00_12

theorem weighted_01_02_00_12 : b4RawGapContribution ![1, 2, 0, 12] = 384 := by
  calc
    b4RawGapContribution ![1, 2, 0, 12] = b4GapPatternWeight 2 0 12 * 32 :=
      b4GapContribution_from_row 1 2 0 12 32 row_01_02_00_12
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_12

def layers_01_02_00_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 23, 28, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 31, 28]]
#print axioms Paper7MomentGapNumeric.layers_01_02_00_13

theorem cells_01_02_00_13 : QTableValid (![1, 3, 3, 16] : Fin 4 → ℕ) layers_01_02_00_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_00_13

theorem valid_01_02_00_13 :
    SparseRowValid (![1, 3, 3, 16] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_02_00_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 3, 16] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 3 + 16 = 23
      decide
    have hzsq : (∑ i, (((![1, 3, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 3^2 + 16^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_00_13
#print axioms Paper7MomentGapNumeric.valid_01_02_00_13

def qvalues_01_02_00_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_00_13

theorem row_01_02_00_13 : b4RowContribution (![1, 3, 3, 16] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 3, 3, 16] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_01_02_00_13) :=
      sparseRow_sound (![1, 3, 3, 16] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_02_00_13) valid_01_02_00_13
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_00_13 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_00_13

theorem weighted_01_02_00_13 : b4RawGapContribution ![1, 2, 0, 13] = 384 := by
  calc
    b4RawGapContribution ![1, 2, 0, 13] = b4GapPatternWeight 2 0 13 * 32 :=
      b4GapContribution_from_row 1 2 0 13 32 row_01_02_00_13
    _ = 384 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_13

theorem row_01_02_00_14 : b4RowContribution (![1, 3, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 17 = 24
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 17^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_14

theorem weighted_01_02_00_14 : b4RawGapContribution ![1, 2, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 14] = b4GapPatternWeight 2 0 14 * 0 :=
      b4GapContribution_from_row 1 2 0 14 0 row_01_02_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_14

theorem row_01_02_00_15 : b4RowContribution (![1, 3, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 18 = 25
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 18^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_15

theorem weighted_01_02_00_15 : b4RawGapContribution ![1, 2, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 15] = b4GapPatternWeight 2 0 15 * 0 :=
      b4GapContribution_from_row 1 2 0 15 0 row_01_02_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_15

theorem row_01_02_00_16 : b4RowContribution (![1, 3, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 19 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 380 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 19^2 = 380
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_16

theorem weighted_01_02_00_16 : b4RawGapContribution ![1, 2, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 16] = b4GapPatternWeight 2 0 16 * 0 :=
      b4GapContribution_from_row 1 2 0 16 0 row_01_02_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_16

theorem row_01_02_00_17 : b4RowContribution (![1, 3, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 20 = 27
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 20^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_17

theorem weighted_01_02_00_17 : b4RawGapContribution ![1, 2, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 17] = b4GapPatternWeight 2 0 17 * 0 :=
      b4GapContribution_from_row 1 2 0 17 0 row_01_02_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_17

theorem row_01_02_00_18 : b4RowContribution (![1, 3, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 21 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 21^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_18

theorem weighted_01_02_00_18 : b4RawGapContribution ![1, 2, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 18] = b4GapPatternWeight 2 0 18 * 0 :=
      b4GapContribution_from_row 1 2 0 18 0 row_01_02_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_18

theorem row_01_02_00_19 : b4RowContribution (![1, 3, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 22] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 22 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 503 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 22^2 = 503
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_19

theorem weighted_01_02_00_19 : b4RawGapContribution ![1, 2, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 19] = b4GapPatternWeight 2 0 19 * 0 :=
      b4GapContribution_from_row 1 2 0 19 0 row_01_02_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_19

theorem row_01_02_00_20 : b4RowContribution (![1, 3, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 23] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 23 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 548 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 23^2 = 548
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_20

theorem weighted_01_02_00_20 : b4RawGapContribution ![1, 2, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 20] = b4GapPatternWeight 2 0 20 * 0 :=
      b4GapContribution_from_row 1 2 0 20 0 row_01_02_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_20

theorem row_01_02_00_21 : b4RowContribution (![1, 3, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 24 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 595 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 24^2 = 595
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_21

theorem weighted_01_02_00_21 : b4RawGapContribution ![1, 2, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 21] = b4GapPatternWeight 2 0 21 * 0 :=
      b4GapContribution_from_row 1 2 0 21 0 row_01_02_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_21

theorem row_01_02_00_22 : b4RowContribution (![1, 3, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 25 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 644 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 25^2 = 644
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_22

theorem weighted_01_02_00_22 : b4RawGapContribution ![1, 2, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 22] = b4GapPatternWeight 2 0 22 * 0 :=
      b4GapContribution_from_row 1 2 0 22 0 row_01_02_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_22

theorem row_01_02_00_23 : b4RowContribution (![1, 3, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 26 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 695 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 26^2 = 695
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_23

theorem weighted_01_02_00_23 : b4RawGapContribution ![1, 2, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 23] = b4GapPatternWeight 2 0 23 * 0 :=
      b4GapContribution_from_row 1 2 0 23 0 row_01_02_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_23

theorem row_01_02_00_24 : b4RowContribution (![1, 3, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 27 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 748 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 27^2 = 748
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_24

theorem weighted_01_02_00_24 : b4RawGapContribution ![1, 2, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 24] = b4GapPatternWeight 2 0 24 * 0 :=
      b4GapContribution_from_row 1 2 0 24 0 row_01_02_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_24

theorem row_01_02_00_25 : b4RowContribution (![1, 3, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 28 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 803 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 28^2 = 803
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_25

theorem weighted_01_02_00_25 : b4RawGapContribution ![1, 2, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 25] = b4GapPatternWeight 2 0 25 * 0 :=
      b4GapContribution_from_row 1 2 0 25 0 row_01_02_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_25

theorem row_01_02_00_26 : b4RowContribution (![1, 3, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 29 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 860 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 29^2 = 860
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_26

theorem weighted_01_02_00_26 : b4RawGapContribution ![1, 2, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 26] = b4GapPatternWeight 2 0 26 * 0 :=
      b4GapContribution_from_row 1 2 0 26 0 row_01_02_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_26

theorem row_01_02_00_27 : b4RowContribution (![1, 3, 3, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 3, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 3 + 30 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 919 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 3^2 + 30^2 = 919
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_00_27

theorem weighted_01_02_00_27 : b4RawGapContribution ![1, 2, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 0, 27] = b4GapPatternWeight 2 0 27 * 0 :=
      b4GapContribution_from_row 1 2 0 27 0 row_01_02_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_00_27

def dvalues_01_02_00 : Fin 28 → ℕ := ![0, 192, 108, 0, 0, 0, 0, 0, 0, 192, 108, 384, 384, 384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_00

theorem dblock_01_02_00 : b4GapPatternDBlock 1 2 0 = 1752 := by
  calc
    b4GapPatternDBlock 1 2 0 = ∑ d : Fin 28, dvalues_01_02_00 d := by
      apply b4GapDBlock_of_rows 1 2 0 dvalues_01_02_00
      intro d
      fin_cases d
      · exact weighted_01_02_00_00
      · exact weighted_01_02_00_01
      · exact weighted_01_02_00_02
      · exact weighted_01_02_00_03
      · exact weighted_01_02_00_04
      · exact weighted_01_02_00_05
      · exact weighted_01_02_00_06
      · exact weighted_01_02_00_07
      · exact weighted_01_02_00_08
      · exact weighted_01_02_00_09
      · exact weighted_01_02_00_10
      · exact weighted_01_02_00_11
      · exact weighted_01_02_00_12
      · exact weighted_01_02_00_13
      · exact weighted_01_02_00_14
      · exact weighted_01_02_00_15
      · exact weighted_01_02_00_16
      · exact weighted_01_02_00_17
      · exact weighted_01_02_00_18
      · exact weighted_01_02_00_19
      · exact weighted_01_02_00_20
      · exact weighted_01_02_00_21
      · exact weighted_01_02_00_22
      · exact weighted_01_02_00_23
      · exact weighted_01_02_00_24
      · exact weighted_01_02_00_25
      · exact weighted_01_02_00_26
      · exact weighted_01_02_00_27
    _ = 1752 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_00

end Paper7MomentGapNumeric
