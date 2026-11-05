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

def layers_00_03_00_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 12, 12, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_00

theorem cells_00_03_00_00 : QTableValid (![0, 3, 3, 3] : Fin 4 → ℕ) layers_00_03_00_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_00

theorem valid_00_03_00_00 :
    SparseRowValid (![0, 3, 3, 3] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 3] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 3 = 9
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 27 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 3^2 = 27
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_00
#print axioms Paper7MomentGapNumeric.valid_00_03_00_00

def qvalues_00_03_00_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_00

theorem row_00_03_00_00 : b4RowContribution (![0, 3, 3, 3] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 3, 3, 3] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_00) :=
      sparseRow_sound (![0, 3, 3, 3] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_00) valid_00_03_00_00
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_00 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_00_00

theorem weighted_00_03_00_00 : b4RawGapContribution ![0, 3, 0, 0] = 4 := by
  calc
    b4RawGapContribution ![0, 3, 0, 0] = b4GapPatternWeight 3 0 0 * 1 :=
      b4GapContribution_from_row 0 3 0 0 1 row_00_03_00_00
    _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_00

def layers_00_03_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 14, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_01

theorem cells_00_03_00_01 : QTableValid (![0, 3, 3, 4] : Fin 4 → ℕ) layers_00_03_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_01

theorem valid_00_03_00_01 :
    SparseRowValid (![0, 3, 3, 4] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_03_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 4] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 4 = 10
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 34 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 4^2 = 34
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_01
#print axioms Paper7MomentGapNumeric.valid_00_03_00_01

def qvalues_00_03_00_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_01

theorem row_00_03_00_01 : b4RowContribution (![0, 3, 3, 4] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 3, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_00_03_00_01) :=
      sparseRow_sound (![0, 3, 3, 4] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_03_00_01) valid_00_03_00_01
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_03_00_01

theorem weighted_00_03_00_01 : b4RawGapContribution ![0, 3, 0, 1] = 12 := by
  calc
    b4RawGapContribution ![0, 3, 0, 1] = b4GapPatternWeight 3 0 1 * 1 :=
      b4GapContribution_from_row 0 3 0 1 1 row_00_03_00_01
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_01

def layers_00_03_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_02

theorem cells_00_03_00_02 : QTableValid (![0, 3, 3, 5] : Fin 4 → ℕ) layers_00_03_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_02

theorem valid_00_03_00_02 :
    SparseRowValid (![0, 3, 3, 5] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 5] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 5 = 11
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 43 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 5^2 = 43
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_02
#print axioms Paper7MomentGapNumeric.valid_00_03_00_02

def qvalues_00_03_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_02

theorem row_00_03_00_02 : b4RowContribution (![0, 3, 3, 5] : Fin 4 → ℕ) = 13 := by
  calc
    b4RowContribution (![0, 3, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_02) :=
      sparseRow_sound (![0, 3, 3, 5] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_02) valid_00_03_00_02
    _ = 13 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_02 Q := by
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
        _ = 13 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_00_02

theorem weighted_00_03_00_02 : b4RawGapContribution ![0, 3, 0, 2] = 156 := by
  calc
    b4RawGapContribution ![0, 3, 0, 2] = b4GapPatternWeight 3 0 2 * 13 :=
      b4GapContribution_from_row 0 3 0 2 13 row_00_03_00_02
    _ = 156 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_02

theorem row_00_03_00_03 : b4RowContribution (![0, 3, 3, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 6] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 6 = 12
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 54 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 6^2 = 54
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_03

theorem weighted_00_03_00_03 : b4RawGapContribution ![0, 3, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 3] = b4GapPatternWeight 3 0 3 * 0 :=
      b4GapContribution_from_row 0 3 0 3 0 row_00_03_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_03

theorem row_00_03_00_04 : b4RowContribution (![0, 3, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 7] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 7 = 13
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 67 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 7^2 = 67
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_04

theorem weighted_00_03_00_04 : b4RawGapContribution ![0, 3, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 4] = b4GapPatternWeight 3 0 4 * 0 :=
      b4GapContribution_from_row 0 3 0 4 0 row_00_03_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_04

theorem row_00_03_00_05 : b4RowContribution (![0, 3, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 8] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 8 = 14
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 8^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_05

theorem weighted_00_03_00_05 : b4RawGapContribution ![0, 3, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 5] = b4GapPatternWeight 3 0 5 * 0 :=
      b4GapContribution_from_row 0 3 0 5 0 row_00_03_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_05

theorem row_00_03_00_06 : b4RowContribution (![0, 3, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 9] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 9 = 15
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 9^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_06

theorem weighted_00_03_00_06 : b4RawGapContribution ![0, 3, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 6] = b4GapPatternWeight 3 0 6 * 0 :=
      b4GapContribution_from_row 0 3 0 6 0 row_00_03_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_06

theorem row_00_03_00_07 : b4RowContribution (![0, 3, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 10] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 10 = 16
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 118 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 10^2 = 118
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_07

theorem weighted_00_03_00_07 : b4RawGapContribution ![0, 3, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 7] = b4GapPatternWeight 3 0 7 * 0 :=
      b4GapContribution_from_row 0 3 0 7 0 row_00_03_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_07

theorem row_00_03_00_08 : b4RowContribution (![0, 3, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 11] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 11 = 17
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 11^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_08

theorem weighted_00_03_00_08 : b4RawGapContribution ![0, 3, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 8] = b4GapPatternWeight 3 0 8 * 0 :=
      b4GapContribution_from_row 0 3 0 8 0 row_00_03_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_08

def layers_00_03_00_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 16, 16, 15, 13, 10, 6, 3, 1]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_09

theorem cells_00_03_00_09 : QTableValid (![0, 3, 3, 12] : Fin 4 → ℕ) layers_00_03_00_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_09

theorem valid_00_03_00_09 :
    SparseRowValid (![0, 3, 3, 12] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_00_03_00_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 12] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 12 = 18
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 12^2 = 162
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_09
#print axioms Paper7MomentGapNumeric.valid_00_03_00_09

def qvalues_00_03_00_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_09

theorem row_00_03_00_09 : b4RowContribution (![0, 3, 3, 12] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 3, 3, 12] : Fin 4 → ℕ) =
        sparseRowValue ({18} : Finset (Fin 19)) (fun _ => layers_00_03_00_09) :=
      sparseRow_sound (![0, 3, 3, 12] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_00_03_00_09) valid_00_03_00_09
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_09 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_03_00_09

theorem weighted_00_03_00_09 : b4RawGapContribution ![0, 3, 0, 9] = 12 := by
  calc
    b4RawGapContribution ![0, 3, 0, 9] = b4GapPatternWeight 3 0 9 * 1 :=
      b4GapContribution_from_row 0 3 0 9 1 row_00_03_00_09
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_09

def layers_00_03_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 16, 16, 16, 15, 13, 10, 6, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_10

theorem cells_00_03_00_10 : QTableValid (![0, 3, 3, 13] : Fin 4 → ℕ) layers_00_03_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_10

theorem valid_00_03_00_10 :
    SparseRowValid (![0, 3, 3, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 13] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 13 = 19
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 13^2 = 187
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_10
#print axioms Paper7MomentGapNumeric.valid_00_03_00_10

def qvalues_00_03_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_10

theorem row_00_03_00_10 : b4RowContribution (![0, 3, 3, 13] : Fin 4 → ℕ) = 13 := by
  calc
    b4RowContribution (![0, 3, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_10) :=
      sparseRow_sound (![0, 3, 3, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_03_00_10) valid_00_03_00_10
    _ = 13 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_10 Q := by
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
        _ = 13 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_00_10

theorem weighted_00_03_00_10 : b4RawGapContribution ![0, 3, 0, 10] = 156 := by
  calc
    b4RawGapContribution ![0, 3, 0, 10] = b4GapPatternWeight 3 0 10 * 13 :=
      b4GapContribution_from_row 0 3 0 10 13 row_00_03_00_10
    _ = 156 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_10

def layers_00_03_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 13, 10, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_11

theorem cells_00_03_00_11 : QTableValid (![0, 3, 3, 14] : Fin 4 → ℕ) layers_00_03_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_11

theorem valid_00_03_00_11 :
    SparseRowValid (![0, 3, 3, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_03_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 14] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 14 = 20
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 14^2 = 214
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_11
#print axioms Paper7MomentGapNumeric.valid_00_03_00_11

def qvalues_00_03_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_11

theorem row_00_03_00_11 : b4RowContribution (![0, 3, 3, 14] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![0, 3, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_00_03_00_11) :=
      sparseRow_sound (![0, 3, 3, 14] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_03_00_11) valid_00_03_00_11
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_11 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_00_11

theorem weighted_00_03_00_11 : b4RawGapContribution ![0, 3, 0, 11] = 192 := by
  calc
    b4RawGapContribution ![0, 3, 0, 11] = b4GapPatternWeight 3 0 11 * 16 :=
      b4GapContribution_from_row 0 3 0 11 16 row_00_03_00_11
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_11

def layers_00_03_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 13, 10]]
#print axioms Paper7MomentGapNumeric.layers_00_03_00_12

theorem cells_00_03_00_12 : QTableValid (![0, 3, 3, 15] : Fin 4 → ℕ) layers_00_03_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_00_12

theorem valid_00_03_00_12 :
    SparseRowValid (![0, 3, 3, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 3, 15] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 3 + 15 = 21
      decide
    have hzsq : (∑ i, (((![0, 3, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 3^2 + 15^2 = 243
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_00_12
#print axioms Paper7MomentGapNumeric.valid_00_03_00_12

def qvalues_00_03_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_00_12

theorem row_00_03_00_12 : b4RowContribution (![0, 3, 3, 15] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![0, 3, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_12) :=
      sparseRow_sound (![0, 3, 3, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_03_00_12) valid_00_03_00_12
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_00_12 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_00_12

theorem weighted_00_03_00_12 : b4RawGapContribution ![0, 3, 0, 12] = 192 := by
  calc
    b4RawGapContribution ![0, 3, 0, 12] = b4GapPatternWeight 3 0 12 * 16 :=
      b4GapContribution_from_row 0 3 0 12 16 row_00_03_00_12
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_12

theorem row_00_03_00_13 : b4RowContribution (![0, 3, 3, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 16] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 16 = 22
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 16^2 = 274
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_13

theorem weighted_00_03_00_13 : b4RawGapContribution ![0, 3, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 13] = b4GapPatternWeight 3 0 13 * 0 :=
      b4GapContribution_from_row 0 3 0 13 0 row_00_03_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_13

theorem row_00_03_00_14 : b4RowContribution (![0, 3, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 17] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 17 = 23
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 17^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_14

theorem weighted_00_03_00_14 : b4RawGapContribution ![0, 3, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 14] = b4GapPatternWeight 3 0 14 * 0 :=
      b4GapContribution_from_row 0 3 0 14 0 row_00_03_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_14

theorem row_00_03_00_15 : b4RowContribution (![0, 3, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 18] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 18 = 24
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 18^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_15

theorem weighted_00_03_00_15 : b4RawGapContribution ![0, 3, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 15] = b4GapPatternWeight 3 0 15 * 0 :=
      b4GapContribution_from_row 0 3 0 15 0 row_00_03_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_15

theorem row_00_03_00_16 : b4RowContribution (![0, 3, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 19] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 19 = 25
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 19^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_16

theorem weighted_00_03_00_16 : b4RawGapContribution ![0, 3, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 16] = b4GapPatternWeight 3 0 16 * 0 :=
      b4GapContribution_from_row 0 3 0 16 0 row_00_03_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_16

theorem row_00_03_00_17 : b4RowContribution (![0, 3, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 20] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 20 = 26
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 20^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_17

theorem weighted_00_03_00_17 : b4RawGapContribution ![0, 3, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 17] = b4GapPatternWeight 3 0 17 * 0 :=
      b4GapContribution_from_row 0 3 0 17 0 row_00_03_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_17

theorem row_00_03_00_18 : b4RowContribution (![0, 3, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 21] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 21 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 21^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_18

theorem weighted_00_03_00_18 : b4RawGapContribution ![0, 3, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 18] = b4GapPatternWeight 3 0 18 * 0 :=
      b4GapContribution_from_row 0 3 0 18 0 row_00_03_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_18

theorem row_00_03_00_19 : b4RowContribution (![0, 3, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 22] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 22 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 22^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_19

theorem weighted_00_03_00_19 : b4RawGapContribution ![0, 3, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 19] = b4GapPatternWeight 3 0 19 * 0 :=
      b4GapContribution_from_row 0 3 0 19 0 row_00_03_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_19

theorem row_00_03_00_20 : b4RowContribution (![0, 3, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 23] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 23 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 23^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_20

theorem weighted_00_03_00_20 : b4RawGapContribution ![0, 3, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 20] = b4GapPatternWeight 3 0 20 * 0 :=
      b4GapContribution_from_row 0 3 0 20 0 row_00_03_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_20

theorem row_00_03_00_21 : b4RowContribution (![0, 3, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 24] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 24 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 594 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 24^2 = 594
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_21

theorem weighted_00_03_00_21 : b4RawGapContribution ![0, 3, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 21] = b4GapPatternWeight 3 0 21 * 0 :=
      b4GapContribution_from_row 0 3 0 21 0 row_00_03_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_21

theorem row_00_03_00_22 : b4RowContribution (![0, 3, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 25] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 25 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 643 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 25^2 = 643
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_22

theorem weighted_00_03_00_22 : b4RawGapContribution ![0, 3, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 22] = b4GapPatternWeight 3 0 22 * 0 :=
      b4GapContribution_from_row 0 3 0 22 0 row_00_03_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_22

theorem row_00_03_00_23 : b4RowContribution (![0, 3, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 26] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 26 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 694 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 26^2 = 694
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_23

theorem weighted_00_03_00_23 : b4RawGapContribution ![0, 3, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 23] = b4GapPatternWeight 3 0 23 * 0 :=
      b4GapContribution_from_row 0 3 0 23 0 row_00_03_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_23

theorem row_00_03_00_24 : b4RowContribution (![0, 3, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 27] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 27 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 747 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 27^2 = 747
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_24

theorem weighted_00_03_00_24 : b4RawGapContribution ![0, 3, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 24] = b4GapPatternWeight 3 0 24 * 0 :=
      b4GapContribution_from_row 0 3 0 24 0 row_00_03_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_24

theorem row_00_03_00_25 : b4RowContribution (![0, 3, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 28] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 28 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 802 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 28^2 = 802
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_25

theorem weighted_00_03_00_25 : b4RawGapContribution ![0, 3, 0, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 25] = b4GapPatternWeight 3 0 25 * 0 :=
      b4GapContribution_from_row 0 3 0 25 0 row_00_03_00_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_25

theorem row_00_03_00_26 : b4RowContribution (![0, 3, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 29] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 29 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 859 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 29^2 = 859
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_26

theorem weighted_00_03_00_26 : b4RawGapContribution ![0, 3, 0, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 26] = b4GapPatternWeight 3 0 26 * 0 :=
      b4GapContribution_from_row 0 3 0 26 0 row_00_03_00_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_26

theorem row_00_03_00_27 : b4RowContribution (![0, 3, 3, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 30] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 30 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 918 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 30^2 = 918
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_27

theorem weighted_00_03_00_27 : b4RawGapContribution ![0, 3, 0, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 27] = b4GapPatternWeight 3 0 27 * 0 :=
      b4GapContribution_from_row 0 3 0 27 0 row_00_03_00_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_27

theorem row_00_03_00_28 : b4RowContribution (![0, 3, 3, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 3, 31] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 3 + 31 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 3, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 979 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 3^2 + 31^2 = 979
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_00_28

theorem weighted_00_03_00_28 : b4RawGapContribution ![0, 3, 0, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 0, 28] = b4GapPatternWeight 3 0 28 * 0 :=
      b4GapContribution_from_row 0 3 0 28 0 row_00_03_00_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_00_28

def dvalues_00_03_00 : Fin 29 → ℕ := ![4, 12, 156, 0, 0, 0, 0, 0, 0, 12, 156, 192, 192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_00

theorem dblock_00_03_00 : b4GapPatternDBlock 0 3 0 = 724 := by
  calc
    b4GapPatternDBlock 0 3 0 = ∑ d : Fin 29, dvalues_00_03_00 d := by
      apply b4GapDBlock_of_rows 0 3 0 dvalues_00_03_00
      intro d
      fin_cases d
      · exact weighted_00_03_00_00
      · exact weighted_00_03_00_01
      · exact weighted_00_03_00_02
      · exact weighted_00_03_00_03
      · exact weighted_00_03_00_04
      · exact weighted_00_03_00_05
      · exact weighted_00_03_00_06
      · exact weighted_00_03_00_07
      · exact weighted_00_03_00_08
      · exact weighted_00_03_00_09
      · exact weighted_00_03_00_10
      · exact weighted_00_03_00_11
      · exact weighted_00_03_00_12
      · exact weighted_00_03_00_13
      · exact weighted_00_03_00_14
      · exact weighted_00_03_00_15
      · exact weighted_00_03_00_16
      · exact weighted_00_03_00_17
      · exact weighted_00_03_00_18
      · exact weighted_00_03_00_19
      · exact weighted_00_03_00_20
      · exact weighted_00_03_00_21
      · exact weighted_00_03_00_22
      · exact weighted_00_03_00_23
      · exact weighted_00_03_00_24
      · exact weighted_00_03_00_25
      · exact weighted_00_03_00_26
      · exact weighted_00_03_00_27
      · exact weighted_00_03_00_28
    _ = 724 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_00

end Paper7MomentGapNumeric
