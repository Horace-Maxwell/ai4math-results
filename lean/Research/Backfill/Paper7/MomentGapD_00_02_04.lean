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

theorem row_00_02_04_00 : b4RowContribution (![0, 2, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 6 = 14
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 76 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 6^2 = 76
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_00

theorem weighted_00_02_04_00 : b4RawGapContribution ![0, 2, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 0] = b4GapPatternWeight 2 4 0 * 0 :=
      b4GapContribution_from_row 0 2 4 0 0 row_00_02_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_00

theorem row_00_02_04_01 : b4RowContribution (![0, 2, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 7 = 15
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 89 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 7^2 = 89
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_01

theorem weighted_00_02_04_01 : b4RawGapContribution ![0, 2, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 1] = b4GapPatternWeight 2 4 1 * 0 :=
      b4GapContribution_from_row 0 2 4 1 0 row_00_02_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_01

theorem row_00_02_04_02 : b4RowContribution (![0, 2, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 8 = 16
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 104 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 8^2 = 104
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_02

theorem weighted_00_02_04_02 : b4RawGapContribution ![0, 2, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 2] = b4GapPatternWeight 2 4 2 * 0 :=
      b4GapContribution_from_row 0 2 4 2 0 row_00_02_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_02

theorem row_00_02_04_03 : b4RowContribution (![0, 2, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 9 = 17
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 121 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 9^2 = 121
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_03

theorem weighted_00_02_04_03 : b4RawGapContribution ![0, 2, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 3] = b4GapPatternWeight 2 4 3 * 0 :=
      b4GapContribution_from_row 0 2 4 3 0 row_00_02_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_03

theorem row_00_02_04_04 : b4RowContribution (![0, 2, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 10 = 18
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 140 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 10^2 = 140
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_04

theorem weighted_00_02_04_04 : b4RawGapContribution ![0, 2, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 4] = b4GapPatternWeight 2 4 4 * 0 :=
      b4GapContribution_from_row 0 2 4 4 0 row_00_02_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_04

def layers_00_02_04_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 21, 20, 18, 15, 12, 9, 6, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_02_04_05

theorem cells_00_02_04_05 : QTableValid (![0, 2, 6, 11] : Fin 4 → ℕ) layers_00_02_04_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_04_05

theorem valid_00_02_04_05 :
    SparseRowValid (![0, 2, 6, 11] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_02_04_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 6, 11] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 6 + 11 = 19
      decide
    have hzsq : (∑ i, (((![0, 2, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 6^2 + 11^2 = 161
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_04_05
#print axioms Paper7MomentGapNumeric.valid_00_02_04_05

def qvalues_00_02_04_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_04_05

theorem row_00_02_04_05 : b4RowContribution (![0, 2, 6, 11] : Fin 4 → ℕ) = 6 := by
  calc
    b4RowContribution (![0, 2, 6, 11] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_00_02_04_05) :=
      sparseRow_sound (![0, 2, 6, 11] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_02_04_05) valid_00_02_04_05
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_04_05 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_04_05

theorem weighted_00_02_04_05 : b4RawGapContribution ![0, 2, 4, 5] = 144 := by
  calc
    b4RawGapContribution ![0, 2, 4, 5] = b4GapPatternWeight 2 4 5 * 6 :=
      b4GapContribution_from_row 0 2 4 5 6 row_00_02_04_05
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_05

def layers_00_02_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 21, 21, 20, 18, 15, 12, 9, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_02_04_06

theorem cells_00_02_04_06 : QTableValid (![0, 2, 6, 12] : Fin 4 → ℕ) layers_00_02_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_04_06

theorem valid_00_02_04_06 :
    SparseRowValid (![0, 2, 6, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_02_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 6, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 6 + 12 = 20
      decide
    have hzsq : (∑ i, (((![0, 2, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 184 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 6^2 + 12^2 = 184
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_04_06
#print axioms Paper7MomentGapNumeric.valid_00_02_04_06

def qvalues_00_02_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_04_06

theorem row_00_02_04_06 : b4RowContribution (![0, 2, 6, 12] : Fin 4 → ℕ) = 12 := by
  calc
    b4RowContribution (![0, 2, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_02_04_06) :=
      sparseRow_sound (![0, 2, 6, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_02_04_06) valid_00_02_04_06
    _ = 12 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_04_06 Q := by
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
        _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_04_06

theorem weighted_00_02_04_06 : b4RawGapContribution ![0, 2, 4, 6] = 288 := by
  calc
    b4RawGapContribution ![0, 2, 4, 6] = b4GapPatternWeight 2 4 6 * 12 :=
      b4GapContribution_from_row 0 2 4 6 12 row_00_02_04_06
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_06

def layers_00_02_04_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 21, 21, 21, 20, 18, 15, 12, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_02_04_07

theorem cells_00_02_04_07 : QTableValid (![0, 2, 6, 13] : Fin 4 → ℕ) layers_00_02_04_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_04_07

theorem valid_00_02_04_07 :
    SparseRowValid (![0, 2, 6, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_02_04_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 6, 13] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 6 + 13 = 21
      decide
    have hzsq : (∑ i, (((![0, 2, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 6^2 + 13^2 = 209
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_04_07
#print axioms Paper7MomentGapNumeric.valid_00_02_04_07

def qvalues_00_02_04_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_04_07

theorem row_00_02_04_07 : b4RowContribution (![0, 2, 6, 13] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![0, 2, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_00_02_04_07) :=
      sparseRow_sound (![0, 2, 6, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_02_04_07) valid_00_02_04_07
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_04_07 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_04_07

theorem weighted_00_02_04_07 : b4RawGapContribution ![0, 2, 4, 7] = 480 := by
  calc
    b4RawGapContribution ![0, 2, 4, 7] = b4GapPatternWeight 2 4 7 * 20 :=
      b4GapContribution_from_row 0 2 4 7 20 row_00_02_04_07
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_07

def layers_00_02_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 21, 21, 21, 21, 20, 18, 15, 12]]
#print axioms Paper7MomentGapNumeric.layers_00_02_04_08

theorem cells_00_02_04_08 : QTableValid (![0, 2, 6, 14] : Fin 4 → ℕ) layers_00_02_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_04_08

theorem valid_00_02_04_08 :
    SparseRowValid (![0, 2, 6, 14] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_02_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 6, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 6 + 14 = 22
      decide
    have hzsq : (∑ i, (((![0, 2, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 6^2 + 14^2 = 236
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_04_08
#print axioms Paper7MomentGapNumeric.valid_00_02_04_08

def qvalues_00_02_04_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_04_08

theorem row_00_02_04_08 : b4RowContribution (![0, 2, 6, 14] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![0, 2, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_02_04_08) :=
      sparseRow_sound (![0, 2, 6, 14] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_02_04_08) valid_00_02_04_08
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_04_08 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_04_08

theorem weighted_00_02_04_08 : b4RawGapContribution ![0, 2, 4, 8] = 864 := by
  calc
    b4RawGapContribution ![0, 2, 4, 8] = b4GapPatternWeight 2 4 8 * 36 :=
      b4GapContribution_from_row 0 2 4 8 36 row_00_02_04_08
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_08

theorem row_00_02_04_09 : b4RowContribution (![0, 2, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 15 = 23
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 15^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_09

theorem weighted_00_02_04_09 : b4RawGapContribution ![0, 2, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 9] = b4GapPatternWeight 2 4 9 * 0 :=
      b4GapContribution_from_row 0 2 4 9 0 row_00_02_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_09

theorem row_00_02_04_10 : b4RowContribution (![0, 2, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 16] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 16 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 296 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 16^2 = 296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_10

theorem weighted_00_02_04_10 : b4RawGapContribution ![0, 2, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 10] = b4GapPatternWeight 2 4 10 * 0 :=
      b4GapContribution_from_row 0 2 4 10 0 row_00_02_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_10

theorem row_00_02_04_11 : b4RowContribution (![0, 2, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 17 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 17^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_11

theorem weighted_00_02_04_11 : b4RawGapContribution ![0, 2, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 11] = b4GapPatternWeight 2 4 11 * 0 :=
      b4GapContribution_from_row 0 2 4 11 0 row_00_02_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_11

theorem row_00_02_04_12 : b4RowContribution (![0, 2, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 18 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 18^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_12

theorem weighted_00_02_04_12 : b4RawGapContribution ![0, 2, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 12] = b4GapPatternWeight 2 4 12 * 0 :=
      b4GapContribution_from_row 0 2 4 12 0 row_00_02_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_12

theorem row_00_02_04_13 : b4RowContribution (![0, 2, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 19 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 19^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_13

theorem weighted_00_02_04_13 : b4RawGapContribution ![0, 2, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 13] = b4GapPatternWeight 2 4 13 * 0 :=
      b4GapContribution_from_row 0 2 4 13 0 row_00_02_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_13

theorem row_00_02_04_14 : b4RowContribution (![0, 2, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 20 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 440 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 20^2 = 440
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_14

theorem weighted_00_02_04_14 : b4RawGapContribution ![0, 2, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 14] = b4GapPatternWeight 2 4 14 * 0 :=
      b4GapContribution_from_row 0 2 4 14 0 row_00_02_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_14

theorem row_00_02_04_15 : b4RowContribution (![0, 2, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 21 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 481 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 21^2 = 481
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_15

theorem weighted_00_02_04_15 : b4RawGapContribution ![0, 2, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 15] = b4GapPatternWeight 2 4 15 * 0 :=
      b4GapContribution_from_row 0 2 4 15 0 row_00_02_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_15

theorem row_00_02_04_16 : b4RowContribution (![0, 2, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 22 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 524 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 22^2 = 524
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_16

theorem weighted_00_02_04_16 : b4RawGapContribution ![0, 2, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 16] = b4GapPatternWeight 2 4 16 * 0 :=
      b4GapContribution_from_row 0 2 4 16 0 row_00_02_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_16

def layers_00_02_04_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21]]
#print axioms Paper7MomentGapNumeric.layers_00_02_04_17

theorem cells_00_02_04_17 : QTableValid (![0, 2, 6, 23] : Fin 4 → ℕ) layers_00_02_04_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_04_17

theorem valid_00_02_04_17 :
    SparseRowValid (![0, 2, 6, 23] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_02_04_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 6, 23] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 6 + 23 = 31
      decide
    have hzsq : (∑ i, (((![0, 2, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 569 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 6^2 + 23^2 = 569
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_04_17
#print axioms Paper7MomentGapNumeric.valid_00_02_04_17

def qvalues_00_02_04_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_04_17

theorem row_00_02_04_17 : b4RowContribution (![0, 2, 6, 23] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 2, 6, 23] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_02_04_17) :=
      sparseRow_sound (![0, 2, 6, 23] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_02_04_17) valid_00_02_04_17
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_04_17 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_04_17

theorem weighted_00_02_04_17 : b4RawGapContribution ![0, 2, 4, 17] = 360 := by
  calc
    b4RawGapContribution ![0, 2, 4, 17] = b4GapPatternWeight 2 4 17 * 15 :=
      b4GapContribution_from_row 0 2 4 17 15 row_00_02_04_17
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_17

theorem row_00_02_04_18 : b4RowContribution (![0, 2, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 24 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 616 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 24^2 = 616
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_18

theorem weighted_00_02_04_18 : b4RawGapContribution ![0, 2, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 18] = b4GapPatternWeight 2 4 18 * 0 :=
      b4GapContribution_from_row 0 2 4 18 0 row_00_02_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_18

theorem row_00_02_04_19 : b4RowContribution (![0, 2, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 25 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 665 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 25^2 = 665
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_19

theorem weighted_00_02_04_19 : b4RawGapContribution ![0, 2, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 19] = b4GapPatternWeight 2 4 19 * 0 :=
      b4GapContribution_from_row 0 2 4 19 0 row_00_02_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_19

theorem row_00_02_04_20 : b4RowContribution (![0, 2, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 26 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 716 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 26^2 = 716
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_20

theorem weighted_00_02_04_20 : b4RawGapContribution ![0, 2, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 20] = b4GapPatternWeight 2 4 20 * 0 :=
      b4GapContribution_from_row 0 2 4 20 0 row_00_02_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_20

theorem row_00_02_04_21 : b4RowContribution (![0, 2, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 27 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 769 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 27^2 = 769
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_21

theorem weighted_00_02_04_21 : b4RawGapContribution ![0, 2, 4, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 21] = b4GapPatternWeight 2 4 21 * 0 :=
      b4GapContribution_from_row 0 2 4 21 0 row_00_02_04_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_21

theorem row_00_02_04_22 : b4RowContribution (![0, 2, 6, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 28 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 824 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 28^2 = 824
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_22

theorem weighted_00_02_04_22 : b4RawGapContribution ![0, 2, 4, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 22] = b4GapPatternWeight 2 4 22 * 0 :=
      b4GapContribution_from_row 0 2 4 22 0 row_00_02_04_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_22

theorem row_00_02_04_23 : b4RowContribution (![0, 2, 6, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 6, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 6 + 29 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 6, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 881 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 6^2 + 29^2 = 881
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_04_23

theorem weighted_00_02_04_23 : b4RawGapContribution ![0, 2, 4, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 4, 23] = b4GapPatternWeight 2 4 23 * 0 :=
      b4GapContribution_from_row 0 2 4 23 0 row_00_02_04_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_04_23

def dvalues_00_02_04 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 144, 288, 480, 864, 0, 0, 0, 0, 0, 0, 0, 0, 360, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_04

theorem dblock_00_02_04 : b4GapPatternDBlock 0 2 4 = 2136 := by
  calc
    b4GapPatternDBlock 0 2 4 = ∑ d : Fin 24, dvalues_00_02_04 d := by
      apply b4GapDBlock_of_rows 0 2 4 dvalues_00_02_04
      intro d
      fin_cases d
      · exact weighted_00_02_04_00
      · exact weighted_00_02_04_01
      · exact weighted_00_02_04_02
      · exact weighted_00_02_04_03
      · exact weighted_00_02_04_04
      · exact weighted_00_02_04_05
      · exact weighted_00_02_04_06
      · exact weighted_00_02_04_07
      · exact weighted_00_02_04_08
      · exact weighted_00_02_04_09
      · exact weighted_00_02_04_10
      · exact weighted_00_02_04_11
      · exact weighted_00_02_04_12
      · exact weighted_00_02_04_13
      · exact weighted_00_02_04_14
      · exact weighted_00_02_04_15
      · exact weighted_00_02_04_16
      · exact weighted_00_02_04_17
      · exact weighted_00_02_04_18
      · exact weighted_00_02_04_19
      · exact weighted_00_02_04_20
      · exact weighted_00_02_04_21
      · exact weighted_00_02_04_22
      · exact weighted_00_02_04_23
    _ = 2136 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_04

end Paper7MomentGapNumeric
