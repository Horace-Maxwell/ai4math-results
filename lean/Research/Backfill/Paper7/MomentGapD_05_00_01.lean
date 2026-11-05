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

theorem row_05_00_01_00 : b4RowContribution (![5, 5, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 6] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 6 = 22
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 6^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_00

theorem weighted_05_00_01_00 : b4RawGapContribution ![5, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 5 0 1 0 0 row_05_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_00

theorem row_05_00_01_01 : b4RowContribution (![5, 5, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 7] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 7 = 23
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 135 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 7^2 = 135
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_01

theorem weighted_05_00_01_01 : b4RawGapContribution ![5, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 5 0 1 1 0 row_05_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_01

theorem row_05_00_01_02 : b4RowContribution (![5, 5, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 8 = 24
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 8^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_02

theorem weighted_05_00_01_02 : b4RawGapContribution ![5, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 5 0 1 2 0 row_05_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_02

theorem row_05_00_01_03 : b4RowContribution (![5, 5, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 9 = 25
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 167 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 9^2 = 167
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_03

theorem weighted_05_00_01_03 : b4RawGapContribution ![5, 0, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 0 :=
      b4GapContribution_from_row 5 0 1 3 0 row_05_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_03

theorem row_05_00_01_04 : b4RowContribution (![5, 5, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 10 = 26
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 10^2 = 186
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_04

theorem weighted_05_00_01_04 : b4RawGapContribution ![5, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 5 0 1 4 0 row_05_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_04

theorem row_05_00_01_05 : b4RowContribution (![5, 5, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 11 = 27
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 11^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_05

theorem weighted_05_00_01_05 : b4RawGapContribution ![5, 0, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 0 :=
      b4GapContribution_from_row 5 0 1 5 0 row_05_00_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_05

def layers_05_00_01_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 26, 29, 30, 29, 26, 21, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 56, 82, 111, 141, 170, 196, 217, 232, 241, 244, 241, 232, 217, 196]]
#print axioms Paper7MomentGapNumeric.layers_05_00_01_06

theorem cells_05_00_01_06 : QTableValid (![5, 5, 6, 12] : Fin 4 → ℕ) layers_05_00_01_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_00_01_06

theorem valid_05_00_01_06 :
    SparseRowValid (![5, 5, 6, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_05_00_01_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 5, 6, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 5 + 5 + 6 + 12 = 28
      decide
    have hzsq : (∑ i, (((![5, 5, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 5^2 + 6^2 + 12^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_00_01_06
#print axioms Paper7MomentGapNumeric.valid_05_00_01_06

def qvalues_05_00_01_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_00_01_06

theorem row_05_00_01_06 : b4RowContribution (![5, 5, 6, 12] : Fin 4 → ℕ) = 56 := by
  calc
    b4RowContribution (![5, 5, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_05_00_01_06) :=
      sparseRow_sound (![5, 5, 6, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_05_00_01_06) valid_05_00_01_06
    _ = 56 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_00_01_06 Q := by
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
        _ = 56 := by decide
#print axioms Paper7MomentGapNumeric.row_05_00_01_06

theorem weighted_05_00_01_06 : b4RawGapContribution ![5, 0, 1, 6] = 672 := by
  calc
    b4RawGapContribution ![5, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 56 :=
      b4GapContribution_from_row 5 0 1 6 56 row_05_00_01_06
    _ = 672 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_06

theorem row_05_00_01_07 : b4RowContribution (![5, 5, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 13 = 29
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 13^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_07

theorem weighted_05_00_01_07 : b4RawGapContribution ![5, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 5 0 1 7 0 row_05_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_07

def layers_05_00_01_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 26, 29, 30, 29, 26, 21, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 56, 82, 111, 141, 170, 196, 217, 232, 242, 248, 250, 248, 242, 232]]
#print axioms Paper7MomentGapNumeric.layers_05_00_01_08

theorem cells_05_00_01_08 : QTableValid (![5, 5, 6, 14] : Fin 4 → ℕ) layers_05_00_01_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_00_01_08

theorem valid_05_00_01_08 :
    SparseRowValid (![5, 5, 6, 14] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_00_01_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 5, 6, 14] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 5 + 5 + 6 + 14 = 30
      decide
    have hzsq : (∑ i, (((![5, 5, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 5^2 + 6^2 + 14^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_00_01_08
#print axioms Paper7MomentGapNumeric.valid_05_00_01_08

def qvalues_05_00_01_08 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_00_01_08

theorem row_05_00_01_08 : b4RowContribution (![5, 5, 6, 14] : Fin 4 → ℕ) = 83 := by
  calc
    b4RowContribution (![5, 5, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_00_01_08) :=
      sparseRow_sound (![5, 5, 6, 14] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_05_00_01_08) valid_05_00_01_08
    _ = 83 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_00_01_08 Q := by
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
        _ = 83 := by decide
#print axioms Paper7MomentGapNumeric.row_05_00_01_08

theorem weighted_05_00_01_08 : b4RawGapContribution ![5, 0, 1, 8] = 996 := by
  calc
    b4RawGapContribution ![5, 0, 1, 8] = b4GapPatternWeight 0 1 8 * 83 :=
      b4GapContribution_from_row 5 0 1 8 83 row_05_00_01_08
    _ = 996 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_08

theorem row_05_00_01_09 : b4RowContribution (![5, 5, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 15 = 31
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 15^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_09

theorem weighted_05_00_01_09 : b4RawGapContribution ![5, 0, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 9] = b4GapPatternWeight 0 1 9 * 0 :=
      b4GapContribution_from_row 5 0 1 9 0 row_05_00_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_09

theorem row_05_00_01_10 : b4RowContribution (![5, 5, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 16 = 32
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 16^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_10

theorem weighted_05_00_01_10 : b4RawGapContribution ![5, 0, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 10] = b4GapPatternWeight 0 1 10 * 0 :=
      b4GapContribution_from_row 5 0 1 10 0 row_05_00_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_10

theorem row_05_00_01_11 : b4RowContribution (![5, 5, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 17 = 33
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 17^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_11

theorem weighted_05_00_01_11 : b4RawGapContribution ![5, 0, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 11] = b4GapPatternWeight 0 1 11 * 0 :=
      b4GapContribution_from_row 5 0 1 11 0 row_05_00_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_11

theorem row_05_00_01_12 : b4RowContribution (![5, 5, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 18 = 34
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 18^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_12

theorem weighted_05_00_01_12 : b4RawGapContribution ![5, 0, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 12] = b4GapPatternWeight 0 1 12 * 0 :=
      b4GapContribution_from_row 5 0 1 12 0 row_05_00_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_12

theorem row_05_00_01_13 : b4RowContribution (![5, 5, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 19 = 35
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 19^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_13

theorem weighted_05_00_01_13 : b4RawGapContribution ![5, 0, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 13] = b4GapPatternWeight 0 1 13 * 0 :=
      b4GapContribution_from_row 5 0 1 13 0 row_05_00_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_13

theorem row_05_00_01_14 : b4RowContribution (![5, 5, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 20 = 36
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 20^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_14

theorem weighted_05_00_01_14 : b4RawGapContribution ![5, 0, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 14] = b4GapPatternWeight 0 1 14 * 0 :=
      b4GapContribution_from_row 5 0 1 14 0 row_05_00_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_14

theorem row_05_00_01_15 : b4RowContribution (![5, 5, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 6, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 6 + 21 = 37
    decide
  have hzsq : (∑ i, (((![5, 5, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 527 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 6^2 + 21^2 = 527
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_01_15

theorem weighted_05_00_01_15 : b4RawGapContribution ![5, 0, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 1, 15] = b4GapPatternWeight 0 1 15 * 0 :=
      b4GapContribution_from_row 5 0 1 15 0 row_05_00_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_01_15

def dvalues_05_00_01 : Fin 16 → ℕ := ![0, 0, 0, 0, 0, 0, 672, 0, 996, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_00_01

theorem dblock_05_00_01 : b4GapPatternDBlock 5 0 1 = 1668 := by
  calc
    b4GapPatternDBlock 5 0 1 = ∑ d : Fin 16, dvalues_05_00_01 d := by
      apply b4GapDBlock_of_rows 5 0 1 dvalues_05_00_01
      intro d
      fin_cases d
      · exact weighted_05_00_01_00
      · exact weighted_05_00_01_01
      · exact weighted_05_00_01_02
      · exact weighted_05_00_01_03
      · exact weighted_05_00_01_04
      · exact weighted_05_00_01_05
      · exact weighted_05_00_01_06
      · exact weighted_05_00_01_07
      · exact weighted_05_00_01_08
      · exact weighted_05_00_01_09
      · exact weighted_05_00_01_10
      · exact weighted_05_00_01_11
      · exact weighted_05_00_01_12
      · exact weighted_05_00_01_13
      · exact weighted_05_00_01_14
      · exact weighted_05_00_01_15
    _ = 1668 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_00_01

end Paper7MomentGapNumeric
