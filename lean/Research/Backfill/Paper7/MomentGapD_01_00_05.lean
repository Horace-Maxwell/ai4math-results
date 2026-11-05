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

theorem row_01_00_05_00 : b4RowContribution (![1, 1, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 6 = 14
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 74 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 6^2 = 74
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_00

theorem weighted_01_00_05_00 : b4RawGapContribution ![1, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 1 0 5 0 0 row_01_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_00

theorem row_01_00_05_01 : b4RowContribution (![1, 1, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 7 = 15
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 87 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 7^2 = 87
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_01

theorem weighted_01_00_05_01 : b4RawGapContribution ![1, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 1 0 5 1 0 row_01_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_01

theorem row_01_00_05_02 : b4RowContribution (![1, 1, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 8 = 16
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 102 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 8^2 = 102
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_02

theorem weighted_01_00_05_02 : b4RawGapContribution ![1, 0, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 0 :=
      b4GapContribution_from_row 1 0 5 2 0 row_01_00_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_02

theorem row_01_00_05_03 : b4RowContribution (![1, 1, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 9 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 119 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 9^2 = 119
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_03

theorem weighted_01_00_05_03 : b4RawGapContribution ![1, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 1 0 5 3 0 row_01_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_03

theorem row_01_00_05_04 : b4RowContribution (![1, 1, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 10 = 18
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 10^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_04

theorem weighted_01_00_05_04 : b4RawGapContribution ![1, 0, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 0 :=
      b4GapContribution_from_row 1 0 5 4 0 row_01_00_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_04

def layers_01_00_05_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 27, 24, 20, 16, 12, 8, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_05

theorem cells_01_00_05_05 : QTableValid (![1, 1, 6, 11] : Fin 4 → ℕ) layers_01_00_05_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_05

theorem valid_01_00_05_05 :
    SparseRowValid (![1, 1, 6, 11] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_05_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 11] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 11 = 19
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 159 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 11^2 = 159
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_05
#print axioms Paper7MomentGapNumeric.valid_01_00_05_05

def qvalues_01_00_05_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_05

theorem row_01_00_05_05 : b4RowContribution (![1, 1, 6, 11] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 1, 6, 11] : Fin 4 → ℕ) =
        sparseRowValue ({18} : Finset (Fin 19)) (fun _ => layers_01_00_05_05) :=
      sparseRow_sound (![1, 1, 6, 11] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_05_05) valid_01_00_05_05
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_05 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_05

theorem weighted_01_00_05_05 : b4RawGapContribution ![1, 0, 5, 5] = 48 := by
  calc
    b4RawGapContribution ![1, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 4 :=
      b4GapContribution_from_row 1 0 5 5 4 row_01_00_05_05
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_05

def layers_01_00_05_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 28, 27, 24, 20, 16, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_06

theorem cells_01_00_05_06 : QTableValid (![1, 1, 6, 12] : Fin 4 → ℕ) layers_01_00_05_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_06

theorem valid_01_00_05_06 :
    SparseRowValid (![1, 1, 6, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_00_05_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 12 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 12^2 = 182
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_06
#print axioms Paper7MomentGapNumeric.valid_01_00_05_06

def qvalues_01_00_05_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_06

theorem row_01_00_05_06 : b4RowContribution (![1, 1, 6, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![1, 1, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_00_05_06) :=
      sparseRow_sound (![1, 1, 6, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_00_05_06) valid_01_00_05_06
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_06 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_06

theorem weighted_01_00_05_06 : b4RawGapContribution ![1, 0, 5, 6] = 240 := by
  calc
    b4RawGapContribution ![1, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 20 :=
      b4GapContribution_from_row 1 0 5 6 20 row_01_00_05_06
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_06

def layers_01_00_05_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 28, 28, 27, 24, 20, 16, 12]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_07

theorem cells_01_00_05_07 : QTableValid (![1, 1, 6, 13] : Fin 4 → ℕ) layers_01_00_05_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_07

theorem valid_01_00_05_07 :
    SparseRowValid (![1, 1, 6, 13] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_00_05_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 13] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 13 = 21
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 13^2 = 207
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_07
#print axioms Paper7MomentGapNumeric.valid_01_00_05_07

def qvalues_01_00_05_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_07

theorem row_01_00_05_07 : b4RowContribution (![1, 1, 6, 13] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_01_00_05_07) :=
      sparseRow_sound (![1, 1, 6, 13] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_01_00_05_07) valid_01_00_05_07
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_07 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_07

theorem weighted_01_00_05_07 : b4RawGapContribution ![1, 0, 5, 7] = 288 := by
  calc
    b4RawGapContribution ![1, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 24 :=
      b4GapContribution_from_row 1 0 5 7 24 row_01_00_05_07
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_07

def layers_01_00_05_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 28, 28, 28, 27, 24, 20, 16]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_08

theorem cells_01_00_05_08 : QTableValid (![1, 1, 6, 14] : Fin 4 → ℕ) layers_01_00_05_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_08

theorem valid_01_00_05_08 :
    SparseRowValid (![1, 1, 6, 14] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_00_05_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 14 = 22
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 14^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_08
#print axioms Paper7MomentGapNumeric.valid_01_00_05_08

def qvalues_01_00_05_08 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_08

theorem row_01_00_05_08 : b4RowContribution (![1, 1, 6, 14] : Fin 4 → ℕ) = 53 := by
  calc
    b4RowContribution (![1, 1, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_00_05_08) :=
      sparseRow_sound (![1, 1, 6, 14] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_00_05_08) valid_01_00_05_08
    _ = 53 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_08 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 53 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_08

theorem weighted_01_00_05_08 : b4RawGapContribution ![1, 0, 5, 8] = 636 := by
  calc
    b4RawGapContribution ![1, 0, 5, 8] = b4GapPatternWeight 0 5 8 * 53 :=
      b4GapContribution_from_row 1 0 5 8 53 row_01_00_05_08
    _ = 636 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_08

theorem row_01_00_05_09 : b4RowContribution (![1, 1, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 15 = 23
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 15^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_09

theorem weighted_01_00_05_09 : b4RawGapContribution ![1, 0, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 9] = b4GapPatternWeight 0 5 9 * 0 :=
      b4GapContribution_from_row 1 0 5 9 0 row_01_00_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_09

theorem row_01_00_05_10 : b4RowContribution (![1, 1, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 16] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 16 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 16^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_10

theorem weighted_01_00_05_10 : b4RawGapContribution ![1, 0, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 10] = b4GapPatternWeight 0 5 10 * 0 :=
      b4GapContribution_from_row 1 0 5 10 0 row_01_00_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_10

theorem row_01_00_05_11 : b4RowContribution (![1, 1, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 17 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 17^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_11

theorem weighted_01_00_05_11 : b4RawGapContribution ![1, 0, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 11] = b4GapPatternWeight 0 5 11 * 0 :=
      b4GapContribution_from_row 1 0 5 11 0 row_01_00_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_11

theorem row_01_00_05_12 : b4RowContribution (![1, 1, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 18 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 18^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_12

theorem weighted_01_00_05_12 : b4RawGapContribution ![1, 0, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 12] = b4GapPatternWeight 0 5 12 * 0 :=
      b4GapContribution_from_row 1 0 5 12 0 row_01_00_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_12

theorem row_01_00_05_13 : b4RowContribution (![1, 1, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 19 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 19^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_13

theorem weighted_01_00_05_13 : b4RawGapContribution ![1, 0, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 13] = b4GapPatternWeight 0 5 13 * 0 :=
      b4GapContribution_from_row 1 0 5 13 0 row_01_00_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_13

theorem row_01_00_05_14 : b4RowContribution (![1, 1, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 20 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 20^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_14

theorem weighted_01_00_05_14 : b4RawGapContribution ![1, 0, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 14] = b4GapPatternWeight 0 5 14 * 0 :=
      b4GapContribution_from_row 1 0 5 14 0 row_01_00_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_14

theorem row_01_00_05_15 : b4RowContribution (![1, 1, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 21 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 479 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 21^2 = 479
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_15

theorem weighted_01_00_05_15 : b4RawGapContribution ![1, 0, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 15] = b4GapPatternWeight 0 5 15 * 0 :=
      b4GapContribution_from_row 1 0 5 15 0 row_01_00_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_15

def layers_01_00_05_16 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_16

theorem cells_01_00_05_16 : QTableValid (![1, 1, 6, 22] : Fin 4 → ℕ) layers_01_00_05_16 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_16

theorem valid_01_00_05_16 :
    SparseRowValid (![1, 1, 6, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_00_05_16) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 22] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 22 = 30
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 522 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 22^2 = 522
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_16
#print axioms Paper7MomentGapNumeric.valid_01_00_05_16

def qvalues_01_00_05_16 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_16

theorem row_01_00_05_16 : b4RowContribution (![1, 1, 6, 22] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 1, 6, 22] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_00_05_16) :=
      sparseRow_sound (![1, 1, 6, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_00_05_16) valid_01_00_05_16
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_16 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_16

theorem weighted_01_00_05_16 : b4RawGapContribution ![1, 0, 5, 16] = 12 := by
  calc
    b4RawGapContribution ![1, 0, 5, 16] = b4GapPatternWeight 0 5 16 * 1 :=
      b4GapContribution_from_row 1 0 5 16 1 row_01_00_05_16
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_16

def layers_01_00_05_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28]]
#print axioms Paper7MomentGapNumeric.layers_01_00_05_17

theorem cells_01_00_05_17 : QTableValid (![1, 1, 6, 23] : Fin 4 → ℕ) layers_01_00_05_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_05_17

theorem valid_01_00_05_17 :
    SparseRowValid (![1, 1, 6, 23] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_00_05_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 6, 23] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 6 + 23 = 31
      decide
    have hzsq : (∑ i, (((![1, 1, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 567 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 6^2 + 23^2 = 567
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_05_17
#print axioms Paper7MomentGapNumeric.valid_01_00_05_17

def qvalues_01_00_05_17 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_05_17

theorem row_01_00_05_17 : b4RowContribution (![1, 1, 6, 23] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![1, 1, 6, 23] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_00_05_17) :=
      sparseRow_sound (![1, 1, 6, 23] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_00_05_17) valid_01_00_05_17
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_05_17 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_05_17

theorem weighted_01_00_05_17 : b4RawGapContribution ![1, 0, 5, 17] = 300 := by
  calc
    b4RawGapContribution ![1, 0, 5, 17] = b4GapPatternWeight 0 5 17 * 25 :=
      b4GapContribution_from_row 1 0 5 17 25 row_01_00_05_17
    _ = 300 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_17

theorem row_01_00_05_18 : b4RowContribution (![1, 1, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 24 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 24^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_18

theorem weighted_01_00_05_18 : b4RawGapContribution ![1, 0, 5, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 18] = b4GapPatternWeight 0 5 18 * 0 :=
      b4GapContribution_from_row 1 0 5 18 0 row_01_00_05_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_18

theorem row_01_00_05_19 : b4RowContribution (![1, 1, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 25 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 663 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 25^2 = 663
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_19

theorem weighted_01_00_05_19 : b4RawGapContribution ![1, 0, 5, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 19] = b4GapPatternWeight 0 5 19 * 0 :=
      b4GapContribution_from_row 1 0 5 19 0 row_01_00_05_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_19

theorem row_01_00_05_20 : b4RowContribution (![1, 1, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 26 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 714 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 26^2 = 714
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_20

theorem weighted_01_00_05_20 : b4RawGapContribution ![1, 0, 5, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 20] = b4GapPatternWeight 0 5 20 * 0 :=
      b4GapContribution_from_row 1 0 5 20 0 row_01_00_05_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_20

theorem row_01_00_05_21 : b4RowContribution (![1, 1, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 27 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 767 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 27^2 = 767
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_21

theorem weighted_01_00_05_21 : b4RawGapContribution ![1, 0, 5, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 21] = b4GapPatternWeight 0 5 21 * 0 :=
      b4GapContribution_from_row 1 0 5 21 0 row_01_00_05_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_21

theorem row_01_00_05_22 : b4RowContribution (![1, 1, 6, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 28 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 822 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 28^2 = 822
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_22

theorem weighted_01_00_05_22 : b4RawGapContribution ![1, 0, 5, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 22] = b4GapPatternWeight 0 5 22 * 0 :=
      b4GapContribution_from_row 1 0 5 22 0 row_01_00_05_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_22

theorem row_01_00_05_23 : b4RowContribution (![1, 1, 6, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 6, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 6 + 29 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 6, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 879 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 6^2 + 29^2 = 879
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_05_23

theorem weighted_01_00_05_23 : b4RawGapContribution ![1, 0, 5, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 5, 23] = b4GapPatternWeight 0 5 23 * 0 :=
      b4GapContribution_from_row 1 0 5 23 0 row_01_00_05_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_05_23

def dvalues_01_00_05 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 48, 240, 288, 636, 0, 0, 0, 0, 0, 0, 0, 12, 300, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_05

theorem dblock_01_00_05 : b4GapPatternDBlock 1 0 5 = 1524 := by
  calc
    b4GapPatternDBlock 1 0 5 = ∑ d : Fin 24, dvalues_01_00_05 d := by
      apply b4GapDBlock_of_rows 1 0 5 dvalues_01_00_05
      intro d
      fin_cases d
      · exact weighted_01_00_05_00
      · exact weighted_01_00_05_01
      · exact weighted_01_00_05_02
      · exact weighted_01_00_05_03
      · exact weighted_01_00_05_04
      · exact weighted_01_00_05_05
      · exact weighted_01_00_05_06
      · exact weighted_01_00_05_07
      · exact weighted_01_00_05_08
      · exact weighted_01_00_05_09
      · exact weighted_01_00_05_10
      · exact weighted_01_00_05_11
      · exact weighted_01_00_05_12
      · exact weighted_01_00_05_13
      · exact weighted_01_00_05_14
      · exact weighted_01_00_05_15
      · exact weighted_01_00_05_16
      · exact weighted_01_00_05_17
      · exact weighted_01_00_05_18
      · exact weighted_01_00_05_19
      · exact weighted_01_00_05_20
      · exact weighted_01_00_05_21
      · exact weighted_01_00_05_22
      · exact weighted_01_00_05_23
    _ = 1524 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_05

end Paper7MomentGapNumeric
