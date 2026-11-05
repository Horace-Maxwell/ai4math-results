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

def layers_01_01_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 25, 25, 21, 15, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_00

theorem cells_01_01_02_00 : QTableValid (![1, 2, 4, 4] : Fin 4 → ℕ) layers_01_01_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_00

theorem valid_01_01_02_00 :
    SparseRowValid (![1, 2, 4, 4] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_01_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 4] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 4 = 11
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 37 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 4^2 = 37
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_00
#print axioms Paper7MomentGapNumeric.valid_01_01_02_00

def qvalues_01_01_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_00

theorem row_01_01_02_00 : b4RowContribution (![1, 2, 4, 4] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![1, 2, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_01_02_00) :=
      sparseRow_sound (![1, 2, 4, 4] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_01_02_00) valid_01_01_02_00
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_00 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_02_00

theorem weighted_01_01_02_00 : b4RawGapContribution ![1, 1, 2, 0] = 252 := by
  calc
    b4RawGapContribution ![1, 1, 2, 0] = b4GapPatternWeight 1 2 0 * 21 :=
      b4GapContribution_from_row 1 1 2 0 21 row_01_01_02_00
    _ = 252 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_00

def layers_01_01_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 26, 28, 26, 21, 15, 9, 4, 1, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_01

theorem cells_01_01_02_01 : QTableValid (![1, 2, 4, 5] : Fin 4 → ℕ) layers_01_01_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_01

theorem valid_01_01_02_01 :
    SparseRowValid (![1, 2, 4, 5] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 5] : Fin 4 → ℕ) i) = 12 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 5 = 12
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 46 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 5^2 = 46
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_01
#print axioms Paper7MomentGapNumeric.valid_01_01_02_01

def qvalues_01_01_02_01 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_01

theorem row_01_01_02_01 : b4RowContribution (![1, 2, 4, 5] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 2, 4, 5] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_01) :=
      sparseRow_sound (![1, 2, 4, 5] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_01) valid_01_01_02_01
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_01_02_01

theorem weighted_01_01_02_01 : b4RawGapContribution ![1, 1, 2, 1] = 96 := by
  calc
    b4RawGapContribution ![1, 1, 2, 1] = b4GapPatternWeight 1 2 1 * 4 :=
      b4GapContribution_from_row 1 1 2 1 4 row_01_01_02_01
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_01

theorem row_01_01_02_02 : b4RowContribution (![1, 2, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 6 = 13
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 57 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 6^2 = 57
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_02

theorem weighted_01_01_02_02 : b4RawGapContribution ![1, 1, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 2] = b4GapPatternWeight 1 2 2 * 0 :=
      b4GapContribution_from_row 1 1 2 2 0 row_01_01_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_02

theorem row_01_01_02_03 : b4RowContribution (![1, 2, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 7 = 14
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 70 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 7^2 = 70
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_03

theorem weighted_01_01_02_03 : b4RawGapContribution ![1, 1, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 3] = b4GapPatternWeight 1 2 3 * 0 :=
      b4GapContribution_from_row 1 1 2 3 0 row_01_01_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_03

theorem row_01_01_02_04 : b4RowContribution (![1, 2, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 8 = 15
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 85 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 8^2 = 85
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_04

theorem weighted_01_01_02_04 : b4RawGapContribution ![1, 1, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 4] = b4GapPatternWeight 1 2 4 * 0 :=
      b4GapContribution_from_row 1 1 2 4 0 row_01_01_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_04

theorem row_01_01_02_05 : b4RowContribution (![1, 2, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 9 = 16
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 102 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 9^2 = 102
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_05

theorem weighted_01_01_02_05 : b4RawGapContribution ![1, 1, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 5] = b4GapPatternWeight 1 2 5 * 0 :=
      b4GapContribution_from_row 1 1 2 5 0 row_01_01_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_05

theorem row_01_01_02_06 : b4RowContribution (![1, 2, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 10 = 17
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 121 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 10^2 = 121
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_06

theorem weighted_01_01_02_06 : b4RawGapContribution ![1, 1, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 6] = b4GapPatternWeight 1 2 6 * 0 :=
      b4GapContribution_from_row 1 1 2 6 0 row_01_01_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_06

theorem row_01_01_02_07 : b4RowContribution (![1, 2, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 11 = 18
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 142 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 11^2 = 142
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_07

theorem weighted_01_01_02_07 : b4RawGapContribution ![1, 1, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 7] = b4GapPatternWeight 1 2 7 * 0 :=
      b4GapContribution_from_row 1 1 2 7 0 row_01_01_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_07

def layers_01_01_02_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 26, 29, 30, 30, 30, 30, 30, 30, 29, 26, 21, 15, 9, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_08

theorem cells_01_01_02_08 : QTableValid (![1, 2, 4, 12] : Fin 4 → ℕ) layers_01_01_02_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_08

theorem valid_01_01_02_08 :
    SparseRowValid (![1, 2, 4, 12] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_02_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 12 = 19
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 12^2 = 165
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_08
#print axioms Paper7MomentGapNumeric.valid_01_01_02_08

def qvalues_01_01_02_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_08

theorem row_01_01_02_08 : b4RowContribution (![1, 2, 4, 12] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![1, 2, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_01_01_02_08) :=
      sparseRow_sound (![1, 2, 4, 12] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_01_02_08) valid_01_01_02_08
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_08 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_02_08

theorem weighted_01_01_02_08 : b4RawGapContribution ![1, 1, 2, 8] = 504 := by
  calc
    b4RawGapContribution ![1, 1, 2, 8] = b4GapPatternWeight 1 2 8 * 21 :=
      b4GapContribution_from_row 1 1 2 8 21 row_01_01_02_08
    _ = 504 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_08

def layers_01_01_02_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 26, 29, 30, 30, 30, 30, 30, 30, 30, 29, 26, 21, 15, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_09

theorem cells_01_01_02_09 : QTableValid (![1, 2, 4, 13] : Fin 4 → ℕ) layers_01_01_02_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_09

theorem valid_01_01_02_09 :
    SparseRowValid (![1, 2, 4, 13] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 13] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 13 = 20
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 13^2 = 190
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_09
#print axioms Paper7MomentGapNumeric.valid_01_01_02_09

def qvalues_01_01_02_09 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_09

theorem row_01_01_02_09 : b4RowContribution (![1, 2, 4, 13] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 2, 4, 13] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_09) :=
      sparseRow_sound (![1, 2, 4, 13] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_01_02_09) valid_01_01_02_09
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_09 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_01_02_09

theorem weighted_01_01_02_09 : b4RawGapContribution ![1, 1, 2, 9] = 96 := by
  calc
    b4RawGapContribution ![1, 1, 2, 9] = b4GapPatternWeight 1 2 9 * 4 :=
      b4GapContribution_from_row 1 1 2 9 4 row_01_01_02_09
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_09

def layers_01_01_02_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 26, 29, 30, 30, 30, 30, 30, 30, 30, 30, 29, 26, 21, 15]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_10

theorem cells_01_01_02_10 : QTableValid (![1, 2, 4, 14] : Fin 4 → ℕ) layers_01_01_02_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_10

theorem valid_01_01_02_10 :
    SparseRowValid (![1, 2, 4, 14] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_01_02_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 14 = 21
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 14^2 = 217
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_10
#print axioms Paper7MomentGapNumeric.valid_01_01_02_10

def qvalues_01_01_02_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 26, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_10

theorem row_01_01_02_10 : b4RowContribution (![1, 2, 4, 14] : Fin 4 → ℕ) = 56 := by
  calc
    b4RowContribution (![1, 2, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_01_02_10) :=
      sparseRow_sound (![1, 2, 4, 14] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_01_01_02_10) valid_01_01_02_10
    _ = 56 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_10 Q := by
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
        _ = 56 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_02_10

theorem weighted_01_01_02_10 : b4RawGapContribution ![1, 1, 2, 10] = 1344 := by
  calc
    b4RawGapContribution ![1, 1, 2, 10] = b4GapPatternWeight 1 2 10 * 56 :=
      b4GapContribution_from_row 1 1 2 10 56 row_01_01_02_10
    _ = 1344 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_10

theorem row_01_01_02_11 : b4RowContribution (![1, 2, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 15] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 15 = 22
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 15^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_11

theorem weighted_01_01_02_11 : b4RawGapContribution ![1, 1, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 11] = b4GapPatternWeight 1 2 11 * 0 :=
      b4GapContribution_from_row 1 1 2 11 0 row_01_01_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_11

def layers_01_01_02_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 26, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 29, 26]]
#print axioms Paper7MomentGapNumeric.layers_01_01_02_12

theorem cells_01_01_02_12 : QTableValid (![1, 2, 4, 16] : Fin 4 → ℕ) layers_01_01_02_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_02_12

theorem valid_01_01_02_12 :
    SparseRowValid (![1, 2, 4, 16] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_01_02_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 4, 16] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 4 + 16 = 23
      decide
    have hzsq : (∑ i, (((![1, 2, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 4^2 + 16^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_02_12
#print axioms Paper7MomentGapNumeric.valid_01_01_02_12

def qvalues_01_01_02_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_02_12

theorem row_01_01_02_12 : b4RowContribution (![1, 2, 4, 16] : Fin 4 → ℕ) = 30 := by
  calc
    b4RowContribution (![1, 2, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_01_01_02_12) :=
      sparseRow_sound (![1, 2, 4, 16] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_01_02_12) valid_01_01_02_12
    _ = 30 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_02_12 Q := by
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
        _ = 30 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_02_12

theorem weighted_01_01_02_12 : b4RawGapContribution ![1, 1, 2, 12] = 720 := by
  calc
    b4RawGapContribution ![1, 1, 2, 12] = b4GapPatternWeight 1 2 12 * 30 :=
      b4GapContribution_from_row 1 1 2 12 30 row_01_01_02_12
    _ = 720 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_12

theorem row_01_01_02_13 : b4RowContribution (![1, 2, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 17 = 24
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 17^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_13

theorem weighted_01_01_02_13 : b4RawGapContribution ![1, 1, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 13] = b4GapPatternWeight 1 2 13 * 0 :=
      b4GapContribution_from_row 1 1 2 13 0 row_01_01_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_13

theorem row_01_01_02_14 : b4RowContribution (![1, 2, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 18 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 18^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_14

theorem weighted_01_01_02_14 : b4RawGapContribution ![1, 1, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 14] = b4GapPatternWeight 1 2 14 * 0 :=
      b4GapContribution_from_row 1 1 2 14 0 row_01_01_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_14

theorem row_01_01_02_15 : b4RowContribution (![1, 2, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 19 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 19^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_15

theorem weighted_01_01_02_15 : b4RawGapContribution ![1, 1, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 15] = b4GapPatternWeight 1 2 15 * 0 :=
      b4GapContribution_from_row 1 1 2 15 0 row_01_01_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_15

theorem row_01_01_02_16 : b4RowContribution (![1, 2, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 20 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 20^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_16

theorem weighted_01_01_02_16 : b4RawGapContribution ![1, 1, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 16] = b4GapPatternWeight 1 2 16 * 0 :=
      b4GapContribution_from_row 1 1 2 16 0 row_01_01_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_16

theorem row_01_01_02_17 : b4RowContribution (![1, 2, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 21 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 21^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_17

theorem weighted_01_01_02_17 : b4RawGapContribution ![1, 1, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 17] = b4GapPatternWeight 1 2 17 * 0 :=
      b4GapContribution_from_row 1 1 2 17 0 row_01_01_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_17

theorem row_01_01_02_18 : b4RowContribution (![1, 2, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 22] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 22 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 22^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_18

theorem weighted_01_01_02_18 : b4RawGapContribution ![1, 1, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 18] = b4GapPatternWeight 1 2 18 * 0 :=
      b4GapContribution_from_row 1 1 2 18 0 row_01_01_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_18

theorem row_01_01_02_19 : b4RowContribution (![1, 2, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 23] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 23 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 23^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_19

theorem weighted_01_01_02_19 : b4RawGapContribution ![1, 1, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 19] = b4GapPatternWeight 1 2 19 * 0 :=
      b4GapContribution_from_row 1 1 2 19 0 row_01_01_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_19

theorem row_01_01_02_20 : b4RowContribution (![1, 2, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 24 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 597 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 24^2 = 597
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_20

theorem weighted_01_01_02_20 : b4RawGapContribution ![1, 1, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 20] = b4GapPatternWeight 1 2 20 * 0 :=
      b4GapContribution_from_row 1 1 2 20 0 row_01_01_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_20

theorem row_01_01_02_21 : b4RowContribution (![1, 2, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 25 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 646 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 25^2 = 646
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_21

theorem weighted_01_01_02_21 : b4RawGapContribution ![1, 1, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 21] = b4GapPatternWeight 1 2 21 * 0 :=
      b4GapContribution_from_row 1 1 2 21 0 row_01_01_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_21

theorem row_01_01_02_22 : b4RowContribution (![1, 2, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 26 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 697 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 26^2 = 697
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_22

theorem weighted_01_01_02_22 : b4RawGapContribution ![1, 1, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 22] = b4GapPatternWeight 1 2 22 * 0 :=
      b4GapContribution_from_row 1 1 2 22 0 row_01_01_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_22

theorem row_01_01_02_23 : b4RowContribution (![1, 2, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 27 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 750 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 27^2 = 750
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_23

theorem weighted_01_01_02_23 : b4RawGapContribution ![1, 1, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 23] = b4GapPatternWeight 1 2 23 * 0 :=
      b4GapContribution_from_row 1 1 2 23 0 row_01_01_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_23

theorem row_01_01_02_24 : b4RowContribution (![1, 2, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 28 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 805 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 28^2 = 805
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_24

theorem weighted_01_01_02_24 : b4RawGapContribution ![1, 1, 2, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 24] = b4GapPatternWeight 1 2 24 * 0 :=
      b4GapContribution_from_row 1 1 2 24 0 row_01_01_02_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_24

theorem row_01_01_02_25 : b4RowContribution (![1, 2, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 29 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 862 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 29^2 = 862
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_25

theorem weighted_01_01_02_25 : b4RawGapContribution ![1, 1, 2, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 25] = b4GapPatternWeight 1 2 25 * 0 :=
      b4GapContribution_from_row 1 1 2 25 0 row_01_01_02_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_25

theorem row_01_01_02_26 : b4RowContribution (![1, 2, 4, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 4, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 4 + 30 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 4, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 921 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 4^2 + 30^2 = 921
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_02_26

theorem weighted_01_01_02_26 : b4RawGapContribution ![1, 1, 2, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 2, 26] = b4GapPatternWeight 1 2 26 * 0 :=
      b4GapContribution_from_row 1 1 2 26 0 row_01_01_02_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_02_26

def dvalues_01_01_02 : Fin 27 → ℕ := ![252, 96, 0, 0, 0, 0, 0, 0, 504, 96, 1344, 0, 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_02

theorem dblock_01_01_02 : b4GapPatternDBlock 1 1 2 = 3012 := by
  calc
    b4GapPatternDBlock 1 1 2 = ∑ d : Fin 27, dvalues_01_01_02 d := by
      apply b4GapDBlock_of_rows 1 1 2 dvalues_01_01_02
      intro d
      fin_cases d
      · exact weighted_01_01_02_00
      · exact weighted_01_01_02_01
      · exact weighted_01_01_02_02
      · exact weighted_01_01_02_03
      · exact weighted_01_01_02_04
      · exact weighted_01_01_02_05
      · exact weighted_01_01_02_06
      · exact weighted_01_01_02_07
      · exact weighted_01_01_02_08
      · exact weighted_01_01_02_09
      · exact weighted_01_01_02_10
      · exact weighted_01_01_02_11
      · exact weighted_01_01_02_12
      · exact weighted_01_01_02_13
      · exact weighted_01_01_02_14
      · exact weighted_01_01_02_15
      · exact weighted_01_01_02_16
      · exact weighted_01_01_02_17
      · exact weighted_01_01_02_18
      · exact weighted_01_01_02_19
      · exact weighted_01_01_02_20
      · exact weighted_01_01_02_21
      · exact weighted_01_01_02_22
      · exact weighted_01_01_02_23
      · exact weighted_01_01_02_24
      · exact weighted_01_01_02_25
      · exact weighted_01_01_02_26
    _ = 3012 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_02

end Paper7MomentGapNumeric
