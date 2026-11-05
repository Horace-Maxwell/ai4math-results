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

theorem row_01_00_02_00 : b4RowContribution (![1, 1, 3, 3] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 3] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 3 = 8
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 20 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 3^2 = 20
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_00

theorem weighted_01_00_02_00 : b4RawGapContribution ![1, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 1 0 2 0 0 row_01_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_00

def layers_01_00_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 15, 12, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_01

theorem cells_01_00_02_01 : QTableValid (![1, 1, 3, 4] : Fin 4 → ℕ) layers_01_00_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_01

theorem valid_01_00_02_01 :
    SparseRowValid (![1, 1, 3, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 4] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 4 = 9
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 27 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 4^2 = 27
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_01
#print axioms Paper7MomentGapNumeric.valid_01_00_02_01

def qvalues_01_00_02_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_01

theorem row_01_00_02_01 : b4RowContribution (![1, 1, 3, 4] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 1, 3, 4] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_01) :=
      sparseRow_sound (![1, 1, 3, 4] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_01) valid_01_00_02_01
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_00_02_01

theorem weighted_01_00_02_01 : b4RawGapContribution ![1, 0, 2, 1] = 12 := by
  calc
    b4RawGapContribution ![1, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 1 :=
      b4GapContribution_from_row 1 0 2 1 1 row_01_00_02_01
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_01

def layers_01_00_02_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 16, 15, 12, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_02

theorem cells_01_00_02_02 : QTableValid (![1, 1, 3, 5] : Fin 4 → ℕ) layers_01_00_02_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_02

theorem valid_01_00_02_02 :
    SparseRowValid (![1, 1, 3, 5] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 5] : Fin 4 → ℕ) i) = 10 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 5 = 10
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 36 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 5^2 = 36
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_02
#print axioms Paper7MomentGapNumeric.valid_01_00_02_02

def qvalues_01_00_02_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_02

theorem row_01_00_02_02 : b4RowContribution (![1, 1, 3, 5] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 1, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_02) :=
      sparseRow_sound (![1, 1, 3, 5] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_02) valid_01_00_02_02
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_02 Q := by
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
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_02_02

theorem weighted_01_00_02_02 : b4RawGapContribution ![1, 0, 2, 2] = 48 := by
  calc
    b4RawGapContribution ![1, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 4 :=
      b4GapContribution_from_row 1 0 2 2 4 row_01_00_02_02
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_02

def layers_01_00_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 16, 16, 15, 12, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_03

theorem cells_01_00_02_03 : QTableValid (![1, 1, 3, 6] : Fin 4 → ℕ) layers_01_00_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_03

theorem valid_01_00_02_03 :
    SparseRowValid (![1, 1, 3, 6] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_00_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 6] : Fin 4 → ℕ) i) = 11 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 6 = 11
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 47 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 6^2 = 47
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_03
#print axioms Paper7MomentGapNumeric.valid_01_00_02_03

def qvalues_01_00_02_03 : Fin 19 → ℕ := ![0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_03

theorem row_01_00_02_03 : b4RowContribution (![1, 1, 3, 6] : Fin 4 → ℕ) = 8 := by
  calc
    b4RowContribution (![1, 1, 3, 6] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_01_00_02_03) :=
      sparseRow_sound (![1, 1, 3, 6] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_01_00_02_03) valid_01_00_02_03
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_03 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_02_03

theorem weighted_01_00_02_03 : b4RawGapContribution ![1, 0, 2, 3] = 96 := by
  calc
    b4RawGapContribution ![1, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 8 :=
      b4GapContribution_from_row 1 0 2 3 8 row_01_00_02_03
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_03

theorem row_01_00_02_04 : b4RowContribution (![1, 1, 3, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 7] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 7 = 12
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 60 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 7^2 = 60
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_04

theorem weighted_01_00_02_04 : b4RawGapContribution ![1, 0, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 0 :=
      b4GapContribution_from_row 1 0 2 4 0 row_01_00_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_04

theorem row_01_00_02_05 : b4RowContribution (![1, 1, 3, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 8] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 8 = 13
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 75 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 8^2 = 75
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_05

theorem weighted_01_00_02_05 : b4RawGapContribution ![1, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 1 0 2 5 0 row_01_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_05

theorem row_01_00_02_06 : b4RowContribution (![1, 1, 3, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 9] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 9 = 14
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 92 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 9^2 = 92
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_06

theorem weighted_01_00_02_06 : b4RawGapContribution ![1, 0, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 6] = b4GapPatternWeight 0 2 6 * 0 :=
      b4GapContribution_from_row 1 0 2 6 0 row_01_00_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_06

theorem row_01_00_02_07 : b4RowContribution (![1, 1, 3, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 10] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 10 = 15
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 111 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 10^2 = 111
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_07

theorem weighted_01_00_02_07 : b4RawGapContribution ![1, 0, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 7] = b4GapPatternWeight 0 2 7 * 0 :=
      b4GapContribution_from_row 1 0 2 7 0 row_01_00_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_07

theorem row_01_00_02_08 : b4RowContribution (![1, 1, 3, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 11] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 11 = 16
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 11^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_08

theorem weighted_01_00_02_08 : b4RawGapContribution ![1, 0, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 8] = b4GapPatternWeight 0 2 8 * 0 :=
      b4GapContribution_from_row 1 0 2 8 0 row_01_00_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_08

theorem row_01_00_02_09 : b4RowContribution (![1, 1, 3, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 12] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 12 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 155 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 12^2 = 155
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_09

theorem weighted_01_00_02_09 : b4RawGapContribution ![1, 0, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 9] = b4GapPatternWeight 0 2 9 * 0 :=
      b4GapContribution_from_row 1 0 2 9 0 row_01_00_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_09

def layers_01_00_02_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 12, 8, 4, 1]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_10

theorem cells_01_00_02_10 : QTableValid (![1, 1, 3, 13] : Fin 4 → ℕ) layers_01_00_02_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_10

theorem valid_01_00_02_10 :
    SparseRowValid (![1, 1, 3, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 13] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 13 = 18
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 13^2 = 180
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_10
#print axioms Paper7MomentGapNumeric.valid_01_00_02_10

def qvalues_01_00_02_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_10

theorem row_01_00_02_10 : b4RowContribution (![1, 1, 3, 13] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 1, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_10) :=
      sparseRow_sound (![1, 1, 3, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_00_02_10) valid_01_00_02_10
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_10 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_00_02_10

theorem weighted_01_00_02_10 : b4RawGapContribution ![1, 0, 2, 10] = 192 := by
  calc
    b4RawGapContribution ![1, 0, 2, 10] = b4GapPatternWeight 0 2 10 * 16 :=
      b4GapContribution_from_row 1 0 2 10 16 row_01_00_02_10
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_10

def layers_01_00_02_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 12, 8, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_11

theorem cells_01_00_02_11 : QTableValid (![1, 1, 3, 14] : Fin 4 → ℕ) layers_01_00_02_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_11

theorem valid_01_00_02_11 :
    SparseRowValid (![1, 1, 3, 14] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_02_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 14] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 14 = 19
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 14^2 = 207
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_11
#print axioms Paper7MomentGapNumeric.valid_01_00_02_11

def qvalues_01_00_02_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_11

theorem row_01_00_02_11 : b4RowContribution (![1, 1, 3, 14] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 1, 3, 14] : Fin 4 → ℕ) =
        sparseRowValue ({18} : Finset (Fin 19)) (fun _ => layers_01_00_02_11) :=
      sparseRow_sound (![1, 1, 3, 14] : Fin 4 → ℕ) ({18} : Finset (Fin 19)) (fun _ => layers_01_00_02_11) valid_01_00_02_11
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_11 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_00_02_11

theorem weighted_01_00_02_11 : b4RawGapContribution ![1, 0, 2, 11] = 48 := by
  calc
    b4RawGapContribution ![1, 0, 2, 11] = b4GapPatternWeight 0 2 11 * 4 :=
      b4GapContribution_from_row 1 0 2 11 4 row_01_00_02_11
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_11

def layers_01_00_02_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 15, 12, 8]]
#print axioms Paper7MomentGapNumeric.layers_01_00_02_12

theorem cells_01_00_02_12 : QTableValid (![1, 1, 3, 15] : Fin 4 → ℕ) layers_01_00_02_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_02_12

theorem valid_01_00_02_12 :
    SparseRowValid (![1, 1, 3, 15] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_02_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 3, 15] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 3 + 15 = 20
      decide
    have hzsq : (∑ i, (((![1, 1, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 3^2 + 15^2 = 236
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_02_12
#print axioms Paper7MomentGapNumeric.valid_01_00_02_12

def qvalues_01_00_02_12 : Fin 19 → ℕ := ![0, 0, 8, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_02_12

theorem row_01_00_02_12 : b4RowContribution (![1, 1, 3, 15] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 1, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_02_12) :=
      sparseRow_sound (![1, 1, 3, 15] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_01_00_02_12) valid_01_00_02_12
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_02_12 Q := by
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
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_02_12

theorem weighted_01_00_02_12 : b4RawGapContribution ![1, 0, 2, 12] = 480 := by
  calc
    b4RawGapContribution ![1, 0, 2, 12] = b4GapPatternWeight 0 2 12 * 40 :=
      b4GapContribution_from_row 1 0 2 12 40 row_01_00_02_12
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_12

theorem row_01_00_02_13 : b4RowContribution (![1, 1, 3, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 16] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 16 = 21
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 16^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_13

theorem weighted_01_00_02_13 : b4RawGapContribution ![1, 0, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 13] = b4GapPatternWeight 0 2 13 * 0 :=
      b4GapContribution_from_row 1 0 2 13 0 row_01_00_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_13

theorem row_01_00_02_14 : b4RowContribution (![1, 1, 3, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 17] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 17 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 17^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_14

theorem weighted_01_00_02_14 : b4RawGapContribution ![1, 0, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 14] = b4GapPatternWeight 0 2 14 * 0 :=
      b4GapContribution_from_row 1 0 2 14 0 row_01_00_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_14

theorem row_01_00_02_15 : b4RowContribution (![1, 1, 3, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 18] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 18 = 23
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 18^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_15

theorem weighted_01_00_02_15 : b4RawGapContribution ![1, 0, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 15] = b4GapPatternWeight 0 2 15 * 0 :=
      b4GapContribution_from_row 1 0 2 15 0 row_01_00_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_15

theorem row_01_00_02_16 : b4RowContribution (![1, 1, 3, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 19] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 19 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 19^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_16

theorem weighted_01_00_02_16 : b4RawGapContribution ![1, 0, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 16] = b4GapPatternWeight 0 2 16 * 0 :=
      b4GapContribution_from_row 1 0 2 16 0 row_01_00_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_16

theorem row_01_00_02_17 : b4RowContribution (![1, 1, 3, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 20] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 20 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 20^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_17

theorem weighted_01_00_02_17 : b4RawGapContribution ![1, 0, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 17] = b4GapPatternWeight 0 2 17 * 0 :=
      b4GapContribution_from_row 1 0 2 17 0 row_01_00_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_17

theorem row_01_00_02_18 : b4RowContribution (![1, 1, 3, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 21] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 21 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 452 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 21^2 = 452
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_18

theorem weighted_01_00_02_18 : b4RawGapContribution ![1, 0, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 18] = b4GapPatternWeight 0 2 18 * 0 :=
      b4GapContribution_from_row 1 0 2 18 0 row_01_00_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_18

theorem row_01_00_02_19 : b4RowContribution (![1, 1, 3, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 22] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 22 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 22^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_19

theorem weighted_01_00_02_19 : b4RawGapContribution ![1, 0, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 19] = b4GapPatternWeight 0 2 19 * 0 :=
      b4GapContribution_from_row 1 0 2 19 0 row_01_00_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_19

theorem row_01_00_02_20 : b4RowContribution (![1, 1, 3, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 23] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 23 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 540 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 23^2 = 540
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_20

theorem weighted_01_00_02_20 : b4RawGapContribution ![1, 0, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 20] = b4GapPatternWeight 0 2 20 * 0 :=
      b4GapContribution_from_row 1 0 2 20 0 row_01_00_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_20

theorem row_01_00_02_21 : b4RowContribution (![1, 1, 3, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 24] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 24 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 24^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_21

theorem weighted_01_00_02_21 : b4RawGapContribution ![1, 0, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 21] = b4GapPatternWeight 0 2 21 * 0 :=
      b4GapContribution_from_row 1 0 2 21 0 row_01_00_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_21

theorem row_01_00_02_22 : b4RowContribution (![1, 1, 3, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 25] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 25 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 636 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 25^2 = 636
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_22

theorem weighted_01_00_02_22 : b4RawGapContribution ![1, 0, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 22] = b4GapPatternWeight 0 2 22 * 0 :=
      b4GapContribution_from_row 1 0 2 22 0 row_01_00_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_22

theorem row_01_00_02_23 : b4RowContribution (![1, 1, 3, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 26] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 26 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 687 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 26^2 = 687
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_23

theorem weighted_01_00_02_23 : b4RawGapContribution ![1, 0, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 23] = b4GapPatternWeight 0 2 23 * 0 :=
      b4GapContribution_from_row 1 0 2 23 0 row_01_00_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_23

theorem row_01_00_02_24 : b4RowContribution (![1, 1, 3, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 27] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 27 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 740 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 27^2 = 740
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_24

theorem weighted_01_00_02_24 : b4RawGapContribution ![1, 0, 2, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 24] = b4GapPatternWeight 0 2 24 * 0 :=
      b4GapContribution_from_row 1 0 2 24 0 row_01_00_02_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_24

theorem row_01_00_02_25 : b4RowContribution (![1, 1, 3, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 28] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 28 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 795 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 28^2 = 795
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_25

theorem weighted_01_00_02_25 : b4RawGapContribution ![1, 0, 2, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 25] = b4GapPatternWeight 0 2 25 * 0 :=
      b4GapContribution_from_row 1 0 2 25 0 row_01_00_02_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_25

theorem row_01_00_02_26 : b4RowContribution (![1, 1, 3, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 29] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 29 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 852 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 29^2 = 852
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_26

theorem weighted_01_00_02_26 : b4RawGapContribution ![1, 0, 2, 26] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 26] = b4GapPatternWeight 0 2 26 * 0 :=
      b4GapContribution_from_row 1 0 2 26 0 row_01_00_02_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_26

theorem row_01_00_02_27 : b4RowContribution (![1, 1, 3, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 30] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 30 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 911 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 30^2 = 911
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_27

theorem weighted_01_00_02_27 : b4RawGapContribution ![1, 0, 2, 27] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 27] = b4GapPatternWeight 0 2 27 * 0 :=
      b4GapContribution_from_row 1 0 2 27 0 row_01_00_02_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_27

theorem row_01_00_02_28 : b4RowContribution (![1, 1, 3, 31] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 31] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 31 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 972 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 31^2 = 972
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_28

theorem weighted_01_00_02_28 : b4RawGapContribution ![1, 0, 2, 28] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 28] = b4GapPatternWeight 0 2 28 * 0 :=
      b4GapContribution_from_row 1 0 2 28 0 row_01_00_02_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_28

theorem row_01_00_02_29 : b4RowContribution (![1, 1, 3, 32] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 3, 32] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 3 + 32 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 3, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1035 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 3^2 + 32^2 = 1035
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_02_29

theorem weighted_01_00_02_29 : b4RawGapContribution ![1, 0, 2, 29] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 2, 29] = b4GapPatternWeight 0 2 29 * 0 :=
      b4GapContribution_from_row 1 0 2 29 0 row_01_00_02_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_02_29

def dvalues_01_00_02 : Fin 30 → ℕ := ![0, 12, 48, 96, 0, 0, 0, 0, 0, 0, 192, 48, 480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_02

theorem dblock_01_00_02 : b4GapPatternDBlock 1 0 2 = 876 := by
  calc
    b4GapPatternDBlock 1 0 2 = ∑ d : Fin 30, dvalues_01_00_02 d := by
      apply b4GapDBlock_of_rows 1 0 2 dvalues_01_00_02
      intro d
      fin_cases d
      · exact weighted_01_00_02_00
      · exact weighted_01_00_02_01
      · exact weighted_01_00_02_02
      · exact weighted_01_00_02_03
      · exact weighted_01_00_02_04
      · exact weighted_01_00_02_05
      · exact weighted_01_00_02_06
      · exact weighted_01_00_02_07
      · exact weighted_01_00_02_08
      · exact weighted_01_00_02_09
      · exact weighted_01_00_02_10
      · exact weighted_01_00_02_11
      · exact weighted_01_00_02_12
      · exact weighted_01_00_02_13
      · exact weighted_01_00_02_14
      · exact weighted_01_00_02_15
      · exact weighted_01_00_02_16
      · exact weighted_01_00_02_17
      · exact weighted_01_00_02_18
      · exact weighted_01_00_02_19
      · exact weighted_01_00_02_20
      · exact weighted_01_00_02_21
      · exact weighted_01_00_02_22
      · exact weighted_01_00_02_23
      · exact weighted_01_00_02_24
      · exact weighted_01_00_02_25
      · exact weighted_01_00_02_26
      · exact weighted_01_00_02_27
      · exact weighted_01_00_02_28
      · exact weighted_01_00_02_29
    _ = 876 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_02

end Paper7MomentGapNumeric
