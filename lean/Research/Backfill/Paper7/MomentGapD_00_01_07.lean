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

theorem row_00_01_07_00 : b4RowContribution (![0, 1, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 8 = 17
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 8^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_00

theorem weighted_00_01_07_00 : b4RawGapContribution ![0, 1, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 0] = b4GapPatternWeight 1 7 0 * 0 :=
      b4GapContribution_from_row 0 1 7 0 0 row_00_01_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_00

theorem row_00_01_07_01 : b4RowContribution (![0, 1, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 9 = 18
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 9^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_01

theorem weighted_00_01_07_01 : b4RawGapContribution ![0, 1, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 1] = b4GapPatternWeight 1 7 1 * 0 :=
      b4GapContribution_from_row 0 1 7 1 0 row_00_01_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_01

def layers_00_01_07_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 17, 15, 13, 11, 9, 7, 5, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_01_07_02

theorem cells_00_01_07_02 : QTableValid (![0, 1, 8, 10] : Fin 4 → ℕ) layers_00_01_07_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_07_02

theorem valid_00_01_07_02 :
    SparseRowValid (![0, 1, 8, 10] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_07_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 8, 10] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 8 + 10 = 19
      decide
    have hzsq : (∑ i, (((![0, 1, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 8^2 + 10^2 = 165
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_07_02
#print axioms Paper7MomentGapNumeric.valid_00_01_07_02

def qvalues_00_01_07_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_07_02

theorem row_00_01_07_02 : b4RowContribution (![0, 1, 8, 10] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 1, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_00_01_07_02) :=
      sparseRow_sound (![0, 1, 8, 10] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_01_07_02) valid_00_01_07_02
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_07_02 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_07_02

theorem weighted_00_01_07_02 : b4RawGapContribution ![0, 1, 7, 2] = 216 := by
  calc
    b4RawGapContribution ![0, 1, 7, 2] = b4GapPatternWeight 1 7 2 * 9 :=
      b4GapContribution_from_row 0 1 7 2 9 row_00_01_07_02
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_02

def layers_00_01_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 18, 17, 15, 13, 11, 9, 7, 5]]
#print axioms Paper7MomentGapNumeric.layers_00_01_07_03

theorem cells_00_01_07_03 : QTableValid (![0, 1, 8, 11] : Fin 4 → ℕ) layers_00_01_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_07_03

theorem valid_00_01_07_03 :
    SparseRowValid (![0, 1, 8, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_01_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 8, 11] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 8 + 11 = 20
      decide
    have hzsq : (∑ i, (((![0, 1, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 8^2 + 11^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_07_03
#print axioms Paper7MomentGapNumeric.valid_00_01_07_03

def qvalues_00_01_07_03 : Fin 19 → ℕ := ![0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_07_03

theorem row_00_01_07_03 : b4RowContribution (![0, 1, 8, 11] : Fin 4 → ℕ) = 7 := by
  calc
    b4RowContribution (![0, 1, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_00_01_07_03) :=
      sparseRow_sound (![0, 1, 8, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_01_07_03) valid_00_01_07_03
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_07_03 Q := by
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
        _ = 7 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_07_03

theorem weighted_00_01_07_03 : b4RawGapContribution ![0, 1, 7, 3] = 168 := by
  calc
    b4RawGapContribution ![0, 1, 7, 3] = b4GapPatternWeight 1 7 3 * 7 :=
      b4GapContribution_from_row 0 1 7 3 7 row_00_01_07_03
    _ = 168 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_03

def layers_00_01_07_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 18, 18, 17, 15, 13, 11, 9, 7]]
#print axioms Paper7MomentGapNumeric.layers_00_01_07_04

theorem cells_00_01_07_04 : QTableValid (![0, 1, 8, 12] : Fin 4 → ℕ) layers_00_01_07_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_07_04

theorem valid_00_01_07_04 :
    SparseRowValid (![0, 1, 8, 12] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_01_07_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 8, 12] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 8 + 12 = 21
      decide
    have hzsq : (∑ i, (((![0, 1, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 8^2 + 12^2 = 209
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_07_04
#print axioms Paper7MomentGapNumeric.valid_00_01_07_04

def qvalues_00_01_07_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_07_04

theorem row_00_01_07_04 : b4RowContribution (![0, 1, 8, 12] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 1, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_00_01_07_04) :=
      sparseRow_sound (![0, 1, 8, 12] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_00_01_07_04) valid_00_01_07_04
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_07_04 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_07_04

theorem weighted_00_01_07_04 : b4RawGapContribution ![0, 1, 7, 4] = 360 := by
  calc
    b4RawGapContribution ![0, 1, 7, 4] = b4GapPatternWeight 1 7 4 * 15 :=
      b4GapContribution_from_row 0 1 7 4 15 row_00_01_07_04
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_04

def layers_00_01_07_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 18, 18, 18, 17, 15, 13, 11, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_01_07_05

theorem cells_00_01_07_05 : QTableValid (![0, 1, 8, 13] : Fin 4 → ℕ) layers_00_01_07_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_07_05

theorem valid_00_01_07_05 :
    SparseRowValid (![0, 1, 8, 13] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_00_01_07_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 8, 13] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 8 + 13 = 22
      decide
    have hzsq : (∑ i, (((![0, 1, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 8^2 + 13^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_07_05
#print axioms Paper7MomentGapNumeric.valid_00_01_07_05

def qvalues_00_01_07_05 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_07_05

theorem row_00_01_07_05 : b4RowContribution (![0, 1, 8, 13] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![0, 1, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_00_01_07_05) :=
      sparseRow_sound (![0, 1, 8, 13] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_00_01_07_05) valid_00_01_07_05
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_07_05 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_07_05

theorem weighted_00_01_07_05 : b4RawGapContribution ![0, 1, 7, 5] = 768 := by
  calc
    b4RawGapContribution ![0, 1, 7, 5] = b4GapPatternWeight 1 7 5 * 32 :=
      b4GapContribution_from_row 0 1 7 5 32 row_00_01_07_05
    _ = 768 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_05

theorem row_00_01_07_06 : b4RowContribution (![0, 1, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 14] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 14 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 14^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_06

theorem weighted_00_01_07_06 : b4RawGapContribution ![0, 1, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 6] = b4GapPatternWeight 1 7 6 * 0 :=
      b4GapContribution_from_row 0 1 7 6 0 row_00_01_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_06

def layers_00_01_07_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 18, 18, 18, 18, 18, 17, 15, 13]]
#print axioms Paper7MomentGapNumeric.layers_00_01_07_07

theorem cells_00_01_07_07 : QTableValid (![0, 1, 8, 15] : Fin 4 → ℕ) layers_00_01_07_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_07_07

theorem valid_00_01_07_07 :
    SparseRowValid (![0, 1, 8, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_07_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 8, 15] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 8 + 15 = 24
      decide
    have hzsq : (∑ i, (((![0, 1, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 8^2 + 15^2 = 290
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_07_07
#print axioms Paper7MomentGapNumeric.valid_00_01_07_07

def qvalues_00_01_07_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_07_07

theorem row_00_01_07_07 : b4RowContribution (![0, 1, 8, 15] : Fin 4 → ℕ) = 18 := by
  calc
    b4RowContribution (![0, 1, 8, 15] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_01_07_07) :=
      sparseRow_sound (![0, 1, 8, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_01_07_07) valid_00_01_07_07
    _ = 18 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_07_07 Q := by
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
        _ = 18 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_07_07

theorem weighted_00_01_07_07 : b4RawGapContribution ![0, 1, 7, 7] = 432 := by
  calc
    b4RawGapContribution ![0, 1, 7, 7] = b4GapPatternWeight 1 7 7 * 18 :=
      b4GapContribution_from_row 0 1 7 7 18 row_00_01_07_07
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_07

theorem row_00_01_07_08 : b4RowContribution (![0, 1, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 16] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 16 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 16^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_08

theorem weighted_00_01_07_08 : b4RawGapContribution ![0, 1, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 8] = b4GapPatternWeight 1 7 8 * 0 :=
      b4GapContribution_from_row 0 1 7 8 0 row_00_01_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_08

theorem row_00_01_07_09 : b4RowContribution (![0, 1, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 17 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 17^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_09

theorem weighted_00_01_07_09 : b4RawGapContribution ![0, 1, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 9] = b4GapPatternWeight 1 7 9 * 0 :=
      b4GapContribution_from_row 0 1 7 9 0 row_00_01_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_09

theorem row_00_01_07_10 : b4RowContribution (![0, 1, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 18 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 18^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_10

theorem weighted_00_01_07_10 : b4RawGapContribution ![0, 1, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 10] = b4GapPatternWeight 1 7 10 * 0 :=
      b4GapContribution_from_row 0 1 7 10 0 row_00_01_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_10

theorem row_00_01_07_11 : b4RowContribution (![0, 1, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 19 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 19^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_11

theorem weighted_00_01_07_11 : b4RawGapContribution ![0, 1, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 11] = b4GapPatternWeight 1 7 11 * 0 :=
      b4GapContribution_from_row 0 1 7 11 0 row_00_01_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_11

theorem row_00_01_07_12 : b4RowContribution (![0, 1, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 20 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 20^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_12

theorem weighted_00_01_07_12 : b4RawGapContribution ![0, 1, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 12] = b4GapPatternWeight 1 7 12 * 0 :=
      b4GapContribution_from_row 0 1 7 12 0 row_00_01_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_12

theorem row_00_01_07_13 : b4RowContribution (![0, 1, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 21 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 21^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_13

theorem weighted_00_01_07_13 : b4RawGapContribution ![0, 1, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 13] = b4GapPatternWeight 1 7 13 * 0 :=
      b4GapContribution_from_row 0 1 7 13 0 row_00_01_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_13

theorem row_00_01_07_14 : b4RowContribution (![0, 1, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 22 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 22^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_14

theorem weighted_00_01_07_14 : b4RawGapContribution ![0, 1, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 14] = b4GapPatternWeight 1 7 14 * 0 :=
      b4GapContribution_from_row 0 1 7 14 0 row_00_01_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_14

theorem row_00_01_07_15 : b4RowContribution (![0, 1, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 23 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 594 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 23^2 = 594
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_15

theorem weighted_00_01_07_15 : b4RawGapContribution ![0, 1, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 15] = b4GapPatternWeight 1 7 15 * 0 :=
      b4GapContribution_from_row 0 1 7 15 0 row_00_01_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_15

theorem row_00_01_07_16 : b4RowContribution (![0, 1, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 24 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 641 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 24^2 = 641
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_16

theorem weighted_00_01_07_16 : b4RawGapContribution ![0, 1, 7, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 16] = b4GapPatternWeight 1 7 16 * 0 :=
      b4GapContribution_from_row 0 1 7 16 0 row_00_01_07_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_16

theorem row_00_01_07_17 : b4RowContribution (![0, 1, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 25 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 690 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 25^2 = 690
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_17

theorem weighted_00_01_07_17 : b4RawGapContribution ![0, 1, 7, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 17] = b4GapPatternWeight 1 7 17 * 0 :=
      b4GapContribution_from_row 0 1 7 17 0 row_00_01_07_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_17

theorem row_00_01_07_18 : b4RowContribution (![0, 1, 8, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 26 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 741 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 26^2 = 741
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_18

theorem weighted_00_01_07_18 : b4RawGapContribution ![0, 1, 7, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 18] = b4GapPatternWeight 1 7 18 * 0 :=
      b4GapContribution_from_row 0 1 7 18 0 row_00_01_07_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_18

theorem row_00_01_07_19 : b4RowContribution (![0, 1, 8, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 27 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 794 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 27^2 = 794
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_19

theorem weighted_00_01_07_19 : b4RawGapContribution ![0, 1, 7, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 19] = b4GapPatternWeight 1 7 19 * 0 :=
      b4GapContribution_from_row 0 1 7 19 0 row_00_01_07_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_19

theorem row_00_01_07_20 : b4RowContribution (![0, 1, 8, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 8, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 8 + 28 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 8, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 849 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 8^2 + 28^2 = 849
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_07_20

theorem weighted_00_01_07_20 : b4RawGapContribution ![0, 1, 7, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 7, 20] = b4GapPatternWeight 1 7 20 * 0 :=
      b4GapContribution_from_row 0 1 7 20 0 row_00_01_07_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_07_20

def dvalues_00_01_07 : Fin 21 → ℕ := ![0, 0, 216, 168, 360, 768, 0, 432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_07

theorem dblock_00_01_07 : b4GapPatternDBlock 0 1 7 = 1944 := by
  calc
    b4GapPatternDBlock 0 1 7 = ∑ d : Fin 21, dvalues_00_01_07 d := by
      apply b4GapDBlock_of_rows 0 1 7 dvalues_00_01_07
      intro d
      fin_cases d
      · exact weighted_00_01_07_00
      · exact weighted_00_01_07_01
      · exact weighted_00_01_07_02
      · exact weighted_00_01_07_03
      · exact weighted_00_01_07_04
      · exact weighted_00_01_07_05
      · exact weighted_00_01_07_06
      · exact weighted_00_01_07_07
      · exact weighted_00_01_07_08
      · exact weighted_00_01_07_09
      · exact weighted_00_01_07_10
      · exact weighted_00_01_07_11
      · exact weighted_00_01_07_12
      · exact weighted_00_01_07_13
      · exact weighted_00_01_07_14
      · exact weighted_00_01_07_15
      · exact weighted_00_01_07_16
      · exact weighted_00_01_07_17
      · exact weighted_00_01_07_18
      · exact weighted_00_01_07_19
      · exact weighted_00_01_07_20
    _ = 1944 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_07

end Paper7MomentGapNumeric
