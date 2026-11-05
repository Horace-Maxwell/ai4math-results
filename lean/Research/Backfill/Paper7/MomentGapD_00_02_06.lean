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

theorem row_00_02_06_00 : b4RowContribution (![0, 2, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 8 = 18
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 8^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_00

theorem weighted_00_02_06_00 : b4RawGapContribution ![0, 2, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 0] = b4GapPatternWeight 2 6 0 * 0 :=
      b4GapContribution_from_row 0 2 6 0 0 row_00_02_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_00

theorem row_00_02_06_01 : b4RowContribution (![0, 2, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 9 = 19
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 9^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_01

theorem weighted_00_02_06_01 : b4RawGapContribution ![0, 2, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 1] = b4GapPatternWeight 2 6 1 * 0 :=
      b4GapContribution_from_row 0 2 6 1 0 row_00_02_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_01

def layers_00_02_06_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 27, 26, 24, 21, 18, 15, 12, 9, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_02_06_02

theorem cells_00_02_06_02 : QTableValid (![0, 2, 8, 10] : Fin 4 → ℕ) layers_00_02_06_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_06_02

theorem valid_00_02_06_02 :
    SparseRowValid (![0, 2, 8, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_06_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 8, 10] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 8 + 10 = 20
      decide
    have hzsq : (∑ i, (((![0, 2, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 168 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 8^2 + 10^2 = 168
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_06_02
#print axioms Paper7MomentGapNumeric.valid_00_02_06_02

def qvalues_00_02_06_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_06_02

theorem row_00_02_06_02 : b4RowContribution (![0, 2, 8, 10] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_02_06_02) :=
      sparseRow_sound (![0, 2, 8, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_06_02) valid_00_02_06_02
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_06_02 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_06_02

theorem weighted_00_02_06_02 : b4RawGapContribution ![0, 2, 6, 2] = 576 := by
  calc
    b4RawGapContribution ![0, 2, 6, 2] = b4GapPatternWeight 2 6 2 * 24 :=
      b4GapContribution_from_row 0 2 6 2 24 row_00_02_06_02
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_02

def layers_00_02_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 27, 27, 26, 24, 21, 18, 15, 12, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_02_06_03

theorem cells_00_02_06_03 : QTableValid (![0, 2, 8, 11] : Fin 4 → ℕ) layers_00_02_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_06_03

theorem valid_00_02_06_03 :
    SparseRowValid (![0, 2, 8, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_02_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 8, 11] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 8 + 11 = 21
      decide
    have hzsq : (∑ i, (((![0, 2, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 8^2 + 11^2 = 189
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_06_03
#print axioms Paper7MomentGapNumeric.valid_00_02_06_03

def qvalues_00_02_06_03 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_06_03

theorem row_00_02_06_03 : b4RowContribution (![0, 2, 8, 11] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 2, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_00_02_06_03) :=
      sparseRow_sound (![0, 2, 8, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_02_06_03) valid_00_02_06_03
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_06_03 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_02_06_03

theorem weighted_00_02_06_03 : b4RawGapContribution ![0, 2, 6, 3] = 24 := by
  calc
    b4RawGapContribution ![0, 2, 6, 3] = b4GapPatternWeight 2 6 3 * 1 :=
      b4GapContribution_from_row 0 2 6 3 1 row_00_02_06_03
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_03

theorem row_00_02_06_04 : b4RowContribution (![0, 2, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 12 = 22
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 212 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 12^2 = 212
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_04

theorem weighted_00_02_06_04 : b4RawGapContribution ![0, 2, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 4] = b4GapPatternWeight 2 6 4 * 0 :=
      b4GapContribution_from_row 0 2 6 4 0 row_00_02_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_04

def layers_00_02_06_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 27, 27, 27, 27, 26, 24, 21, 18, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_02_06_05

theorem cells_00_02_06_05 : QTableValid (![0, 2, 8, 13] : Fin 4 → ℕ) layers_00_02_06_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_06_05

theorem valid_00_02_06_05 :
    SparseRowValid (![0, 2, 8, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_02_06_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 8, 13] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 8 + 13 = 23
      decide
    have hzsq : (∑ i, (((![0, 2, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 8^2 + 13^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_06_05
#print axioms Paper7MomentGapNumeric.valid_00_02_06_05

def qvalues_00_02_06_05 : Fin 19 → ℕ := ![0, 0, 0, 9, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_06_05

theorem row_00_02_06_05 : b4RowContribution (![0, 2, 8, 13] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![0, 2, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_02_06_05) :=
      sparseRow_sound (![0, 2, 8, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_02_06_05) valid_00_02_06_05
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_06_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_06_05

theorem weighted_00_02_06_05 : b4RawGapContribution ![0, 2, 6, 5] = 840 := by
  calc
    b4RawGapContribution ![0, 2, 6, 5] = b4GapPatternWeight 2 6 5 * 35 :=
      b4GapContribution_from_row 0 2 6 5 35 row_00_02_06_05
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_05

theorem row_00_02_06_06 : b4RowContribution (![0, 2, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 14] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 14 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 264 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 14^2 = 264
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_06

theorem weighted_00_02_06_06 : b4RawGapContribution ![0, 2, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 6] = b4GapPatternWeight 2 6 6 * 0 :=
      b4GapContribution_from_row 0 2 6 6 0 row_00_02_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_06

theorem row_00_02_06_07 : b4RowContribution (![0, 2, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 15 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 15^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_07

theorem weighted_00_02_06_07 : b4RawGapContribution ![0, 2, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 7] = b4GapPatternWeight 2 6 7 * 0 :=
      b4GapContribution_from_row 0 2 6 7 0 row_00_02_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_07

theorem row_00_02_06_08 : b4RowContribution (![0, 2, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 16 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 16^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_08

theorem weighted_00_02_06_08 : b4RawGapContribution ![0, 2, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 8] = b4GapPatternWeight 2 6 8 * 0 :=
      b4GapContribution_from_row 0 2 6 8 0 row_00_02_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_08

theorem row_00_02_06_09 : b4RowContribution (![0, 2, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 17 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 17^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_09

theorem weighted_00_02_06_09 : b4RawGapContribution ![0, 2, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 9] = b4GapPatternWeight 2 6 9 * 0 :=
      b4GapContribution_from_row 0 2 6 9 0 row_00_02_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_09

theorem row_00_02_06_10 : b4RowContribution (![0, 2, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 18 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 392 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 18^2 = 392
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_10

theorem weighted_00_02_06_10 : b4RawGapContribution ![0, 2, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 10] = b4GapPatternWeight 2 6 10 * 0 :=
      b4GapContribution_from_row 0 2 6 10 0 row_00_02_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_10

theorem row_00_02_06_11 : b4RowContribution (![0, 2, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 19 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 19^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_11

theorem weighted_00_02_06_11 : b4RawGapContribution ![0, 2, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 11] = b4GapPatternWeight 2 6 11 * 0 :=
      b4GapContribution_from_row 0 2 6 11 0 row_00_02_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_11

theorem row_00_02_06_12 : b4RowContribution (![0, 2, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 20 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 20^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_12

theorem weighted_00_02_06_12 : b4RawGapContribution ![0, 2, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 12] = b4GapPatternWeight 2 6 12 * 0 :=
      b4GapContribution_from_row 0 2 6 12 0 row_00_02_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_12

theorem row_00_02_06_13 : b4RowContribution (![0, 2, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 21 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 509 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 21^2 = 509
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_13

theorem weighted_00_02_06_13 : b4RawGapContribution ![0, 2, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 13] = b4GapPatternWeight 2 6 13 * 0 :=
      b4GapContribution_from_row 0 2 6 13 0 row_00_02_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_13

theorem row_00_02_06_14 : b4RowContribution (![0, 2, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 22 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 552 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 22^2 = 552
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_14

theorem weighted_00_02_06_14 : b4RawGapContribution ![0, 2, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 14] = b4GapPatternWeight 2 6 14 * 0 :=
      b4GapContribution_from_row 0 2 6 14 0 row_00_02_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_14

theorem row_00_02_06_15 : b4RowContribution (![0, 2, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 23 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 597 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 23^2 = 597
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_15

theorem weighted_00_02_06_15 : b4RawGapContribution ![0, 2, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 15] = b4GapPatternWeight 2 6 15 * 0 :=
      b4GapContribution_from_row 0 2 6 15 0 row_00_02_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_15

theorem row_00_02_06_16 : b4RowContribution (![0, 2, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 24 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 644 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 24^2 = 644
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_16

theorem weighted_00_02_06_16 : b4RawGapContribution ![0, 2, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 16] = b4GapPatternWeight 2 6 16 * 0 :=
      b4GapContribution_from_row 0 2 6 16 0 row_00_02_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_16

theorem row_00_02_06_17 : b4RowContribution (![0, 2, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 25 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 693 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 25^2 = 693
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_17

theorem weighted_00_02_06_17 : b4RawGapContribution ![0, 2, 6, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 17] = b4GapPatternWeight 2 6 17 * 0 :=
      b4GapContribution_from_row 0 2 6 17 0 row_00_02_06_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_17

theorem row_00_02_06_18 : b4RowContribution (![0, 2, 8, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 26 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 744 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 26^2 = 744
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_18

theorem weighted_00_02_06_18 : b4RawGapContribution ![0, 2, 6, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 18] = b4GapPatternWeight 2 6 18 * 0 :=
      b4GapContribution_from_row 0 2 6 18 0 row_00_02_06_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_18

theorem row_00_02_06_19 : b4RowContribution (![0, 2, 8, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 8, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 8 + 27 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 8, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 797 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 8^2 + 27^2 = 797
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_06_19

theorem weighted_00_02_06_19 : b4RawGapContribution ![0, 2, 6, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 6, 19] = b4GapPatternWeight 2 6 19 * 0 :=
      b4GapContribution_from_row 0 2 6 19 0 row_00_02_06_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_06_19

def dvalues_00_02_06 : Fin 20 → ℕ := ![0, 0, 576, 24, 0, 840, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_06

theorem dblock_00_02_06 : b4GapPatternDBlock 0 2 6 = 1440 := by
  calc
    b4GapPatternDBlock 0 2 6 = ∑ d : Fin 20, dvalues_00_02_06 d := by
      apply b4GapDBlock_of_rows 0 2 6 dvalues_00_02_06
      intro d
      fin_cases d
      · exact weighted_00_02_06_00
      · exact weighted_00_02_06_01
      · exact weighted_00_02_06_02
      · exact weighted_00_02_06_03
      · exact weighted_00_02_06_04
      · exact weighted_00_02_06_05
      · exact weighted_00_02_06_06
      · exact weighted_00_02_06_07
      · exact weighted_00_02_06_08
      · exact weighted_00_02_06_09
      · exact weighted_00_02_06_10
      · exact weighted_00_02_06_11
      · exact weighted_00_02_06_12
      · exact weighted_00_02_06_13
      · exact weighted_00_02_06_14
      · exact weighted_00_02_06_15
      · exact weighted_00_02_06_16
      · exact weighted_00_02_06_17
      · exact weighted_00_02_06_18
      · exact weighted_00_02_06_19
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_06

end Paper7MomentGapNumeric
