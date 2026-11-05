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

def layers_01_00_03_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 18, 16, 12, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_00

theorem cells_01_00_03_00 : QTableValid (![1, 1, 4, 4] : Fin 4 → ℕ) layers_01_00_03_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_00

theorem valid_01_00_03_00 :
    SparseRowValid (![1, 1, 4, 4] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_03_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 4] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 4 = 10
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 34 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 4^2 = 34
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_00
#print axioms Paper7MomentGapNumeric.valid_01_00_03_00

def qvalues_01_00_03_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_00

theorem row_01_00_03_00 : b4RowContribution (![1, 1, 4, 4] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 1, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_00_03_00) :=
      sparseRow_sound (![1, 1, 4, 4] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_03_00) valid_01_00_03_00
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_00_03_00

theorem weighted_01_00_03_00 : b4RawGapContribution ![1, 0, 3, 0] = 6 := by
  calc
    b4RawGapContribution ![1, 0, 3, 0] = b4GapPatternWeight 0 3 0 * 1 :=
      b4GapContribution_from_row 1 0 3 0 1 row_01_00_03_00
    _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_00

def layers_01_00_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 19, 19, 16, 12, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_01

theorem cells_01_00_03_01 : QTableValid (![1, 1, 4, 5] : Fin 4 → ℕ) layers_01_00_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_01

theorem valid_01_00_03_01 :
    SparseRowValid (![1, 1, 4, 5] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 5] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 5 = 11
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 43 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 5^2 = 43
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_01
#print axioms Paper7MomentGapNumeric.valid_01_00_03_01

def qvalues_01_00_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_01

theorem row_01_00_03_01 : b4RowContribution (![1, 1, 4, 5] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 1, 4, 5] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_01) :=
      sparseRow_sound (![1, 1, 4, 5] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_01) valid_01_00_03_01
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_01 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_03_01

theorem weighted_01_00_03_01 : b4RawGapContribution ![1, 0, 3, 1] = 192 := by
  calc
    b4RawGapContribution ![1, 0, 3, 1] = b4GapPatternWeight 0 3 1 * 16 :=
      b4GapContribution_from_row 1 0 3 1 16 row_01_00_03_01
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_01

theorem row_01_00_03_02 : b4RowContribution (![1, 1, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 6] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 6 = 12
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 54 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 6^2 = 54
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_02

theorem weighted_01_00_03_02 : b4RawGapContribution ![1, 0, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 2] = b4GapPatternWeight 0 3 2 * 0 :=
      b4GapContribution_from_row 1 0 3 2 0 row_01_00_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_02

theorem row_01_00_03_03 : b4RowContribution (![1, 1, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 7] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 7 = 13
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 67 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 7^2 = 67
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_03

theorem weighted_01_00_03_03 : b4RawGapContribution ![1, 0, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 3] = b4GapPatternWeight 0 3 3 * 0 :=
      b4GapContribution_from_row 1 0 3 3 0 row_01_00_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_03

theorem row_01_00_03_04 : b4RowContribution (![1, 1, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 8] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 8 = 14
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 8^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_04

theorem weighted_01_00_03_04 : b4RawGapContribution ![1, 0, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 4] = b4GapPatternWeight 0 3 4 * 0 :=
      b4GapContribution_from_row 1 0 3 4 0 row_01_00_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_04

theorem row_01_00_03_05 : b4RowContribution (![1, 1, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 9] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 9 = 15
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 9^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_05

theorem weighted_01_00_03_05 : b4RawGapContribution ![1, 0, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 5] = b4GapPatternWeight 0 3 5 * 0 :=
      b4GapContribution_from_row 1 0 3 5 0 row_01_00_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_05

theorem row_01_00_03_06 : b4RowContribution (![1, 1, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 10] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 10 = 16
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 118 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 10^2 = 118
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_06

theorem weighted_01_00_03_06 : b4RawGapContribution ![1, 0, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 6] = b4GapPatternWeight 0 3 6 * 0 :=
      b4GapContribution_from_row 1 0 3 6 0 row_01_00_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_06

theorem row_01_00_03_07 : b4RowContribution (![1, 1, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 11] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 11 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 11^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_07

theorem weighted_01_00_03_07 : b4RawGapContribution ![1, 0, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 7] = b4GapPatternWeight 0 3 7 * 0 :=
      b4GapContribution_from_row 1 0 3 7 0 row_01_00_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_07

def layers_01_00_03_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 19, 20, 20, 20, 20, 20, 20, 20, 19, 16, 12, 8, 4, 1]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_08

theorem cells_01_00_03_08 : QTableValid (![1, 1, 4, 12] : Fin 4 → ℕ) layers_01_00_03_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_08

theorem valid_01_00_03_08 :
    SparseRowValid (![1, 1, 4, 12] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_03_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 12] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 12 = 18
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 12^2 = 162
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_08
#print axioms Paper7MomentGapNumeric.valid_01_00_03_08

def qvalues_01_00_03_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_08

theorem row_01_00_03_08 : b4RowContribution (![1, 1, 4, 12] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 1, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({18} : Finset (Fin 19)) (fun _ => layers_01_00_03_08) :=
      sparseRow_sound (![1, 1, 4, 12] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_03_08) valid_01_00_03_08
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_08 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_03_08

theorem weighted_01_00_03_08 : b4RawGapContribution ![1, 0, 3, 8] = 12 := by
  calc
    b4RawGapContribution ![1, 0, 3, 8] = b4GapPatternWeight 0 3 8 * 1 :=
      b4GapContribution_from_row 1 0 3 8 1 row_01_00_03_08
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_08

def layers_01_00_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 19, 20, 20, 20, 20, 20, 20, 20, 20, 19, 16, 12, 8, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_09

theorem cells_01_00_03_09 : QTableValid (![1, 1, 4, 13] : Fin 4 → ℕ) layers_01_00_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_09

theorem valid_01_00_03_09 :
    SparseRowValid (![1, 1, 4, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 13] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 13 = 19
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 13^2 = 187
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_09
#print axioms Paper7MomentGapNumeric.valid_01_00_03_09

def qvalues_01_00_03_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_09

theorem row_01_00_03_09 : b4RowContribution (![1, 1, 4, 13] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 1, 4, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_09) :=
      sparseRow_sound (![1, 1, 4, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_00_03_09) valid_01_00_03_09
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_09 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_03_09

theorem weighted_01_00_03_09 : b4RawGapContribution ![1, 0, 3, 9] = 192 := by
  calc
    b4RawGapContribution ![1, 0, 3, 9] = b4GapPatternWeight 0 3 9 * 16 :=
      b4GapContribution_from_row 1 0 3 9 16 row_01_00_03_09
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_09

def layers_01_00_03_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 16, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_10

theorem cells_01_00_03_10 : QTableValid (![1, 1, 4, 14] : Fin 4 → ℕ) layers_01_00_03_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_10

theorem valid_01_00_03_10 :
    SparseRowValid (![1, 1, 4, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_03_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 14] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 14 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 14^2 = 214
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_10
#print axioms Paper7MomentGapNumeric.valid_01_00_03_10

def qvalues_01_00_03_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_10

theorem row_01_00_03_10 : b4RowContribution (![1, 1, 4, 14] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![1, 1, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_01_00_03_10) :=
      sparseRow_sound (![1, 1, 4, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_00_03_10) valid_01_00_03_10
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_10 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_03_10

theorem weighted_01_00_03_10 : b4RawGapContribution ![1, 0, 3, 10] = 240 := by
  calc
    b4RawGapContribution ![1, 0, 3, 10] = b4GapPatternWeight 0 3 10 * 20 :=
      b4GapContribution_from_row 1 0 3 10 20 row_01_00_03_10
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_10

def layers_01_00_03_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 16, 12]]
#print axioms Paper7MomentGapNumeric.layers_01_00_03_11

theorem cells_01_00_03_11 : QTableValid (![1, 1, 4, 15] : Fin 4 → ℕ) layers_01_00_03_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_03_11

theorem valid_01_00_03_11 :
    SparseRowValid (![1, 1, 4, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_03_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 4, 15] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 4 + 15 = 21
      decide
    have hzsq : (∑ i, (((![1, 1, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 4^2 + 15^2 = 243
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_03_11
#print axioms Paper7MomentGapNumeric.valid_01_00_03_11

def qvalues_01_00_03_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_03_11

theorem row_01_00_03_11 : b4RowContribution (![1, 1, 4, 15] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![1, 1, 4, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_03_11) :=
      sparseRow_sound (![1, 1, 4, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_03_11) valid_01_00_03_11
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_03_11 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_03_11

theorem weighted_01_00_03_11 : b4RawGapContribution ![1, 0, 3, 11] = 240 := by
  calc
    b4RawGapContribution ![1, 0, 3, 11] = b4GapPatternWeight 0 3 11 * 20 :=
      b4GapContribution_from_row 1 0 3 11 20 row_01_00_03_11
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_11

theorem row_01_00_03_12 : b4RowContribution (![1, 1, 4, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 16] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 16 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 16^2 = 274
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_12

theorem weighted_01_00_03_12 : b4RawGapContribution ![1, 0, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 12] = b4GapPatternWeight 0 3 12 * 0 :=
      b4GapContribution_from_row 1 0 3 12 0 row_01_00_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_12

theorem row_01_00_03_13 : b4RowContribution (![1, 1, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 17] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 17 = 23
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 17^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_13

theorem weighted_01_00_03_13 : b4RawGapContribution ![1, 0, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 13] = b4GapPatternWeight 0 3 13 * 0 :=
      b4GapContribution_from_row 1 0 3 13 0 row_01_00_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_13

theorem row_01_00_03_14 : b4RowContribution (![1, 1, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 18] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 18 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 18^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_14

theorem weighted_01_00_03_14 : b4RawGapContribution ![1, 0, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 14] = b4GapPatternWeight 0 3 14 * 0 :=
      b4GapContribution_from_row 1 0 3 14 0 row_01_00_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_14

theorem row_01_00_03_15 : b4RowContribution (![1, 1, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 19] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 19 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 19^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_15

theorem weighted_01_00_03_15 : b4RawGapContribution ![1, 0, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 15] = b4GapPatternWeight 0 3 15 * 0 :=
      b4GapContribution_from_row 1 0 3 15 0 row_01_00_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_15

theorem row_01_00_03_16 : b4RowContribution (![1, 1, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 20] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 20 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 20^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_16

theorem weighted_01_00_03_16 : b4RawGapContribution ![1, 0, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 16] = b4GapPatternWeight 0 3 16 * 0 :=
      b4GapContribution_from_row 1 0 3 16 0 row_01_00_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_16

theorem row_01_00_03_17 : b4RowContribution (![1, 1, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 21] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 21 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 21^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_17

theorem weighted_01_00_03_17 : b4RawGapContribution ![1, 0, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 17] = b4GapPatternWeight 0 3 17 * 0 :=
      b4GapContribution_from_row 1 0 3 17 0 row_01_00_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_17

theorem row_01_00_03_18 : b4RowContribution (![1, 1, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 22] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 22 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 22^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_18

theorem weighted_01_00_03_18 : b4RawGapContribution ![1, 0, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 18] = b4GapPatternWeight 0 3 18 * 0 :=
      b4GapContribution_from_row 1 0 3 18 0 row_01_00_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_18

theorem row_01_00_03_19 : b4RowContribution (![1, 1, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 23] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 23 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 23^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_19

theorem weighted_01_00_03_19 : b4RawGapContribution ![1, 0, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 19] = b4GapPatternWeight 0 3 19 * 0 :=
      b4GapContribution_from_row 1 0 3 19 0 row_01_00_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_19

theorem row_01_00_03_20 : b4RowContribution (![1, 1, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 24] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 24 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 594 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 24^2 = 594
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_20

theorem weighted_01_00_03_20 : b4RawGapContribution ![1, 0, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 20] = b4GapPatternWeight 0 3 20 * 0 :=
      b4GapContribution_from_row 1 0 3 20 0 row_01_00_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_20

theorem row_01_00_03_21 : b4RowContribution (![1, 1, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 25] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 25 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 643 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 25^2 = 643
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_21

theorem weighted_01_00_03_21 : b4RawGapContribution ![1, 0, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 21] = b4GapPatternWeight 0 3 21 * 0 :=
      b4GapContribution_from_row 1 0 3 21 0 row_01_00_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_21

theorem row_01_00_03_22 : b4RowContribution (![1, 1, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 26] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 26 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 694 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 26^2 = 694
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_22

theorem weighted_01_00_03_22 : b4RawGapContribution ![1, 0, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 22] = b4GapPatternWeight 0 3 22 * 0 :=
      b4GapContribution_from_row 1 0 3 22 0 row_01_00_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_22

theorem row_01_00_03_23 : b4RowContribution (![1, 1, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 27] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 27 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 747 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 27^2 = 747
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_23

theorem weighted_01_00_03_23 : b4RawGapContribution ![1, 0, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 23] = b4GapPatternWeight 0 3 23 * 0 :=
      b4GapContribution_from_row 1 0 3 23 0 row_01_00_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_23

theorem row_01_00_03_24 : b4RowContribution (![1, 1, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 28] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 28 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 802 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 28^2 = 802
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_24

theorem weighted_01_00_03_24 : b4RawGapContribution ![1, 0, 3, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 24] = b4GapPatternWeight 0 3 24 * 0 :=
      b4GapContribution_from_row 1 0 3 24 0 row_01_00_03_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_24

theorem row_01_00_03_25 : b4RowContribution (![1, 1, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 29] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 29 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 859 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 29^2 = 859
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_25

theorem weighted_01_00_03_25 : b4RawGapContribution ![1, 0, 3, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 25] = b4GapPatternWeight 0 3 25 * 0 :=
      b4GapContribution_from_row 1 0 3 25 0 row_01_00_03_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_25

theorem row_01_00_03_26 : b4RowContribution (![1, 1, 4, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 30] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 30 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 918 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 30^2 = 918
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_26

theorem weighted_01_00_03_26 : b4RawGapContribution ![1, 0, 3, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 26] = b4GapPatternWeight 0 3 26 * 0 :=
      b4GapContribution_from_row 1 0 3 26 0 row_01_00_03_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_26

theorem row_01_00_03_27 : b4RowContribution (![1, 1, 4, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 4, 31] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 4 + 31 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 4, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 979 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 4^2 + 31^2 = 979
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_03_27

theorem weighted_01_00_03_27 : b4RawGapContribution ![1, 0, 3, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 3, 27] = b4GapPatternWeight 0 3 27 * 0 :=
      b4GapContribution_from_row 1 0 3 27 0 row_01_00_03_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_03_27

def dvalues_01_00_03 : Fin 28 → ℕ := ![6, 192, 0, 0, 0, 0, 0, 0, 12, 192, 240, 240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_03

theorem dblock_01_00_03 : b4GapPatternDBlock 1 0 3 = 882 := by
  calc
    b4GapPatternDBlock 1 0 3 = ∑ d : Fin 28, dvalues_01_00_03 d := by
      apply b4GapDBlock_of_rows 1 0 3 dvalues_01_00_03
      intro d
      fin_cases d
      · exact weighted_01_00_03_00
      · exact weighted_01_00_03_01
      · exact weighted_01_00_03_02
      · exact weighted_01_00_03_03
      · exact weighted_01_00_03_04
      · exact weighted_01_00_03_05
      · exact weighted_01_00_03_06
      · exact weighted_01_00_03_07
      · exact weighted_01_00_03_08
      · exact weighted_01_00_03_09
      · exact weighted_01_00_03_10
      · exact weighted_01_00_03_11
      · exact weighted_01_00_03_12
      · exact weighted_01_00_03_13
      · exact weighted_01_00_03_14
      · exact weighted_01_00_03_15
      · exact weighted_01_00_03_16
      · exact weighted_01_00_03_17
      · exact weighted_01_00_03_18
      · exact weighted_01_00_03_19
      · exact weighted_01_00_03_20
      · exact weighted_01_00_03_21
      · exact weighted_01_00_03_22
      · exact weighted_01_00_03_23
      · exact weighted_01_00_03_24
      · exact weighted_01_00_03_25
      · exact weighted_01_00_03_26
      · exact weighted_01_00_03_27
    _ = 882 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_03

end Paper7MomentGapNumeric
