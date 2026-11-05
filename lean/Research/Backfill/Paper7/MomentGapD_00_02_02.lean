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

def layers_00_02_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 13, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_00

theorem cells_00_02_02_00 : QTableValid (![0, 2, 4, 4] : Fin 4 → ℕ) layers_00_02_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_00

theorem valid_00_02_02_00 :
    SparseRowValid (![0, 2, 4, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 4] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 4 = 10
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 36 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 4^2 = 36
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_00
#print axioms Paper7MomentGapNumeric.valid_00_02_02_00

def qvalues_00_02_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_00

theorem row_00_02_02_00 : b4RowContribution (![0, 2, 4, 4] : Fin 4 → ℕ) = 3 := by
  calc
    b4RowContribution (![0, 2, 4, 4] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_02_02_00) :=
      sparseRow_sound (![0, 2, 4, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_02_00) valid_00_02_02_00
    _ = 3 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_00 Q := by
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
        _ = 3 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_00

theorem weighted_00_02_02_00 : b4RawGapContribution ![0, 2, 2, 0] = 36 := by
  calc
    b4RawGapContribution ![0, 2, 2, 0] = b4GapPatternWeight 2 2 0 * 3 :=
      b4GapContribution_from_row 0 2 2 0 3 row_00_02_02_00
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_00

def layers_00_02_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_01

theorem cells_00_02_02_01 : QTableValid (![0, 2, 4, 5] : Fin 4 → ℕ) layers_00_02_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_01

theorem valid_00_02_02_01 :
    SparseRowValid (![0, 2, 4, 5] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 5] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 5 = 11
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 45 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 5^2 = 45
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_01
#print axioms Paper7MomentGapNumeric.valid_00_02_02_01

def qvalues_00_02_02_01 : Fin 19 → ℕ := ![0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_01

theorem row_00_02_02_01 : b4RowContribution (![0, 2, 4, 5] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 2, 4, 5] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_01) :=
      sparseRow_sound (![0, 2, 4, 5] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_01) valid_00_02_02_01
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_01 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_01

theorem weighted_00_02_02_01 : b4RawGapContribution ![0, 2, 2, 1] = 216 := by
  calc
    b4RawGapContribution ![0, 2, 2, 1] = b4GapPatternWeight 2 2 1 * 9 :=
      b4GapContribution_from_row 0 2 2 1 9 row_00_02_02_01
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_01

theorem row_00_02_02_02 : b4RowContribution (![0, 2, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 6] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 6 = 12
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 56 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 6^2 = 56
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_02

theorem weighted_00_02_02_02 : b4RawGapContribution ![0, 2, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 2] = b4GapPatternWeight 2 2 2 * 0 :=
      b4GapContribution_from_row 0 2 2 2 0 row_00_02_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_02

theorem row_00_02_02_03 : b4RowContribution (![0, 2, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 7] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 7 = 13
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 69 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 7^2 = 69
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_03

theorem weighted_00_02_02_03 : b4RawGapContribution ![0, 2, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 3] = b4GapPatternWeight 2 2 3 * 0 :=
      b4GapContribution_from_row 0 2 2 3 0 row_00_02_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_03

theorem row_00_02_02_04 : b4RowContribution (![0, 2, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 8] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 8 = 14
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 84 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 8^2 = 84
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_04

theorem weighted_00_02_02_04 : b4RawGapContribution ![0, 2, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 4] = b4GapPatternWeight 2 2 4 * 0 :=
      b4GapContribution_from_row 0 2 2 4 0 row_00_02_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_04

theorem row_00_02_02_05 : b4RowContribution (![0, 2, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 9] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 9 = 15
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 101 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 9^2 = 101
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_05

theorem weighted_00_02_02_05 : b4RawGapContribution ![0, 2, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 5] = b4GapPatternWeight 2 2 5 * 0 :=
      b4GapContribution_from_row 0 2 2 5 0 row_00_02_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_05

theorem row_00_02_02_06 : b4RowContribution (![0, 2, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 10] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 10 = 16
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 120 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 10^2 = 120
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_06

theorem weighted_00_02_02_06 : b4RawGapContribution ![0, 2, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 6] = b4GapPatternWeight 2 2 6 * 0 :=
      b4GapContribution_from_row 0 2 2 6 0 row_00_02_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_06

theorem row_00_02_02_07 : b4RowContribution (![0, 2, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 11] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 11 = 17
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 141 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 11^2 = 141
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_07

theorem weighted_00_02_02_07 : b4RawGapContribution ![0, 2, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 7] = b4GapPatternWeight 2 2 7 * 0 :=
      b4GapContribution_from_row 0 2 2 7 0 row_00_02_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_07

def layers_00_02_02_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 15, 14, 12, 9, 6, 3, 1]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_08

theorem cells_00_02_02_08 : QTableValid (![0, 2, 4, 12] : Fin 4 → ℕ) layers_00_02_02_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_08

theorem valid_00_02_02_08 :
    SparseRowValid (![0, 2, 4, 12] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_02_02_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 12] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 12 = 18
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 12^2 = 164
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_08
#print axioms Paper7MomentGapNumeric.valid_00_02_02_08

def qvalues_00_02_02_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_08

theorem row_00_02_02_08 : b4RowContribution (![0, 2, 4, 12] : Fin 4 → ℕ) = 3 := by
  calc
    b4RowContribution (![0, 2, 4, 12] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_00_02_02_08) :=
      sparseRow_sound (![0, 2, 4, 12] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_00_02_02_08) valid_00_02_02_08
    _ = 3 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_08 Q := by
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
        _ = 3 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_08

theorem weighted_00_02_02_08 : b4RawGapContribution ![0, 2, 2, 8] = 72 := by
  calc
    b4RawGapContribution ![0, 2, 2, 8] = b4GapPatternWeight 2 2 8 * 3 :=
      b4GapContribution_from_row 0 2 2 8 3 row_00_02_02_08
    _ = 72 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_08

def layers_00_02_02_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 14, 12, 9, 6, 3]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_09

theorem cells_00_02_02_09 : QTableValid (![0, 2, 4, 13] : Fin 4 → ℕ) layers_00_02_02_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_09

theorem valid_00_02_02_09 :
    SparseRowValid (![0, 2, 4, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 13] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 13 = 19
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 13^2 = 189
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_09
#print axioms Paper7MomentGapNumeric.valid_00_02_02_09

def qvalues_00_02_02_09 : Fin 19 → ℕ := ![0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_09

theorem row_00_02_02_09 : b4RowContribution (![0, 2, 4, 13] : Fin 4 → ℕ) = 9 := by
  calc
    b4RowContribution (![0, 2, 4, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_09) :=
      sparseRow_sound (![0, 2, 4, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_00_02_02_09) valid_00_02_02_09
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_09 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_09

theorem weighted_00_02_02_09 : b4RawGapContribution ![0, 2, 2, 9] = 216 := by
  calc
    b4RawGapContribution ![0, 2, 2, 9] = b4GapPatternWeight 2 2 9 * 9 :=
      b4GapContribution_from_row 0 2 2 9 9 row_00_02_02_09
    _ = 216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_09

def layers_00_02_02_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 12, 9, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_10

theorem cells_00_02_02_10 : QTableValid (![0, 2, 4, 14] : Fin 4 → ℕ) layers_00_02_02_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_10

theorem valid_00_02_02_10 :
    SparseRowValid (![0, 2, 4, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_02_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 14] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 14 = 20
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 216 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 14^2 = 216
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_10
#print axioms Paper7MomentGapNumeric.valid_00_02_02_10

def qvalues_00_02_02_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_10

theorem row_00_02_02_10 : b4RowContribution (![0, 2, 4, 14] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 2, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_02_02_10) :=
      sparseRow_sound (![0, 2, 4, 14] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_02_10) valid_00_02_02_10
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_10 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_10

theorem weighted_00_02_02_10 : b4RawGapContribution ![0, 2, 2, 10] = 360 := by
  calc
    b4RawGapContribution ![0, 2, 2, 10] = b4GapPatternWeight 2 2 10 * 15 :=
      b4GapContribution_from_row 0 2 2 10 15 row_00_02_02_10
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_10

def layers_00_02_02_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 12, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_11

theorem cells_00_02_02_11 : QTableValid (![0, 2, 4, 15] : Fin 4 → ℕ) layers_00_02_02_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_11

theorem valid_00_02_02_11 :
    SparseRowValid (![0, 2, 4, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_02_02_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 15] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 15 = 21
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 15^2 = 245
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_11
#print axioms Paper7MomentGapNumeric.valid_00_02_02_11

def qvalues_00_02_02_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_11

theorem row_00_02_02_11 : b4RowContribution (![0, 2, 4, 15] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 2, 4, 15] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_02_02_11) :=
      sparseRow_sound (![0, 2, 4, 15] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_02_02_11) valid_00_02_02_11
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_11 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_11

theorem weighted_00_02_02_11 : b4RawGapContribution ![0, 2, 2, 11] = 360 := by
  calc
    b4RawGapContribution ![0, 2, 2, 11] = b4GapPatternWeight 2 2 11 * 15 :=
      b4GapContribution_from_row 0 2 2 11 15 row_00_02_02_11
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_11

def layers_00_02_02_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 12]]
#print axioms Paper7MomentGapNumeric.layers_00_02_02_12

theorem cells_00_02_02_12 : QTableValid (![0, 2, 4, 16] : Fin 4 → ℕ) layers_00_02_02_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_02_12

theorem valid_00_02_02_12 :
    SparseRowValid (![0, 2, 4, 16] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_02_02_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 4, 16] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 4 + 16 = 22
      decide
    have hzsq : (∑ i, (((![0, 2, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 4^2 + 16^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_02_12
#print axioms Paper7MomentGapNumeric.valid_00_02_02_12

def qvalues_00_02_02_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_02_12

theorem row_00_02_02_12 : b4RowContribution (![0, 2, 4, 16] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 2, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_00_02_02_12) :=
      sparseRow_sound (![0, 2, 4, 16] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_02_02_12) valid_00_02_02_12
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_02_12 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_02_12

theorem weighted_00_02_02_12 : b4RawGapContribution ![0, 2, 2, 12] = 360 := by
  calc
    b4RawGapContribution ![0, 2, 2, 12] = b4GapPatternWeight 2 2 12 * 15 :=
      b4GapContribution_from_row 0 2 2 12 15 row_00_02_02_12
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_12

theorem row_00_02_02_13 : b4RowContribution (![0, 2, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 17] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 17 = 23
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 17^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_13

theorem weighted_00_02_02_13 : b4RawGapContribution ![0, 2, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 13] = b4GapPatternWeight 2 2 13 * 0 :=
      b4GapContribution_from_row 0 2 2 13 0 row_00_02_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_13

theorem row_00_02_02_14 : b4RowContribution (![0, 2, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 18] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 18 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 344 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 18^2 = 344
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_14

theorem weighted_00_02_02_14 : b4RawGapContribution ![0, 2, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 14] = b4GapPatternWeight 2 2 14 * 0 :=
      b4GapContribution_from_row 0 2 2 14 0 row_00_02_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_14

theorem row_00_02_02_15 : b4RowContribution (![0, 2, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 19] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 19 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 19^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_15

theorem weighted_00_02_02_15 : b4RawGapContribution ![0, 2, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 15] = b4GapPatternWeight 2 2 15 * 0 :=
      b4GapContribution_from_row 0 2 2 15 0 row_00_02_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_15

theorem row_00_02_02_16 : b4RowContribution (![0, 2, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 20] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 20 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 20^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_16

theorem weighted_00_02_02_16 : b4RawGapContribution ![0, 2, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 16] = b4GapPatternWeight 2 2 16 * 0 :=
      b4GapContribution_from_row 0 2 2 16 0 row_00_02_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_16

theorem row_00_02_02_17 : b4RowContribution (![0, 2, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 21] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 21 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 21^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_17

theorem weighted_00_02_02_17 : b4RawGapContribution ![0, 2, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 17] = b4GapPatternWeight 2 2 17 * 0 :=
      b4GapContribution_from_row 0 2 2 17 0 row_00_02_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_17

theorem row_00_02_02_18 : b4RowContribution (![0, 2, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 22] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 22 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 504 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 22^2 = 504
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_18

theorem weighted_00_02_02_18 : b4RawGapContribution ![0, 2, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 18] = b4GapPatternWeight 2 2 18 * 0 :=
      b4GapContribution_from_row 0 2 2 18 0 row_00_02_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_18

theorem row_00_02_02_19 : b4RowContribution (![0, 2, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 23] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 23 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 23^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_19

theorem weighted_00_02_02_19 : b4RawGapContribution ![0, 2, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 19] = b4GapPatternWeight 2 2 19 * 0 :=
      b4GapContribution_from_row 0 2 2 19 0 row_00_02_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_19

theorem row_00_02_02_20 : b4RowContribution (![0, 2, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 24] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 24 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 596 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 24^2 = 596
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_20

theorem weighted_00_02_02_20 : b4RawGapContribution ![0, 2, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 20] = b4GapPatternWeight 2 2 20 * 0 :=
      b4GapContribution_from_row 0 2 2 20 0 row_00_02_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_20

theorem row_00_02_02_21 : b4RowContribution (![0, 2, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 25] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 25 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 645 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 25^2 = 645
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_21

theorem weighted_00_02_02_21 : b4RawGapContribution ![0, 2, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 21] = b4GapPatternWeight 2 2 21 * 0 :=
      b4GapContribution_from_row 0 2 2 21 0 row_00_02_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_21

theorem row_00_02_02_22 : b4RowContribution (![0, 2, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 26] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 26 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 696 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 26^2 = 696
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_22

theorem weighted_00_02_02_22 : b4RawGapContribution ![0, 2, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 22] = b4GapPatternWeight 2 2 22 * 0 :=
      b4GapContribution_from_row 0 2 2 22 0 row_00_02_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_22

theorem row_00_02_02_23 : b4RowContribution (![0, 2, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 27] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 27 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 749 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 27^2 = 749
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_23

theorem weighted_00_02_02_23 : b4RawGapContribution ![0, 2, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 23] = b4GapPatternWeight 2 2 23 * 0 :=
      b4GapContribution_from_row 0 2 2 23 0 row_00_02_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_23

theorem row_00_02_02_24 : b4RowContribution (![0, 2, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 28] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 28 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 804 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 28^2 = 804
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_24

theorem weighted_00_02_02_24 : b4RawGapContribution ![0, 2, 2, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 24] = b4GapPatternWeight 2 2 24 * 0 :=
      b4GapContribution_from_row 0 2 2 24 0 row_00_02_02_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_24

theorem row_00_02_02_25 : b4RowContribution (![0, 2, 4, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 29] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 29 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 861 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 29^2 = 861
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_25

theorem weighted_00_02_02_25 : b4RawGapContribution ![0, 2, 2, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 25] = b4GapPatternWeight 2 2 25 * 0 :=
      b4GapContribution_from_row 0 2 2 25 0 row_00_02_02_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_25

theorem row_00_02_02_26 : b4RowContribution (![0, 2, 4, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 30] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 30 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 920 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 30^2 = 920
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_26

theorem weighted_00_02_02_26 : b4RawGapContribution ![0, 2, 2, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 26] = b4GapPatternWeight 2 2 26 * 0 :=
      b4GapContribution_from_row 0 2 2 26 0 row_00_02_02_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_26

theorem row_00_02_02_27 : b4RowContribution (![0, 2, 4, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 4, 31] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 4 + 31 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 4, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 981 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 4^2 + 31^2 = 981
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_02_27

theorem weighted_00_02_02_27 : b4RawGapContribution ![0, 2, 2, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 2, 27] = b4GapPatternWeight 2 2 27 * 0 :=
      b4GapContribution_from_row 0 2 2 27 0 row_00_02_02_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_02_27

def dvalues_00_02_02 : Fin 28 → ℕ := ![36, 216, 0, 0, 0, 0, 0, 0, 72, 216, 360, 360, 360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_02

theorem dblock_00_02_02 : b4GapPatternDBlock 0 2 2 = 1620 := by
  calc
    b4GapPatternDBlock 0 2 2 = ∑ d : Fin 28, dvalues_00_02_02 d := by
      apply b4GapDBlock_of_rows 0 2 2 dvalues_00_02_02
      intro d
      fin_cases d
      · exact weighted_00_02_02_00
      · exact weighted_00_02_02_01
      · exact weighted_00_02_02_02
      · exact weighted_00_02_02_03
      · exact weighted_00_02_02_04
      · exact weighted_00_02_02_05
      · exact weighted_00_02_02_06
      · exact weighted_00_02_02_07
      · exact weighted_00_02_02_08
      · exact weighted_00_02_02_09
      · exact weighted_00_02_02_10
      · exact weighted_00_02_02_11
      · exact weighted_00_02_02_12
      · exact weighted_00_02_02_13
      · exact weighted_00_02_02_14
      · exact weighted_00_02_02_15
      · exact weighted_00_02_02_16
      · exact weighted_00_02_02_17
      · exact weighted_00_02_02_18
      · exact weighted_00_02_02_19
      · exact weighted_00_02_02_20
      · exact weighted_00_02_02_21
      · exact weighted_00_02_02_22
      · exact weighted_00_02_02_23
      · exact weighted_00_02_02_24
      · exact weighted_00_02_02_25
      · exact weighted_00_02_02_26
      · exact weighted_00_02_02_27
    _ = 1620 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_02

end Paper7MomentGapNumeric
