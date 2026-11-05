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

theorem row_06_00_01_00 : b4RowContribution (![6, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 7] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 7 = 26
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_00

theorem weighted_06_00_01_00 : b4RawGapContribution ![6, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 6 0 1 0 0 row_06_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_00

theorem row_06_00_01_01 : b4RowContribution (![6, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 8] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 8 = 27
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_01

theorem weighted_06_00_01_01 : b4RawGapContribution ![6, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 6 0 1 1 0 row_06_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_01

theorem row_06_00_01_02 : b4RowContribution (![6, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 9 = 28
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_02

theorem weighted_06_00_01_02 : b4RawGapContribution ![6, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 6 0 1 2 0 row_06_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_02

def layers_06_00_01_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 34, 38, 40, 40, 38, 34, 28, 21, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 56, 84, 118, 156, 196, 236, 273, 304, 326, 337, 337, 326, 304, 273]]
#print axioms Paper7MomentGapNumeric.layers_06_00_01_03

theorem cells_06_00_01_03 : QTableValid (![6, 6, 7, 10] : Fin 4 → ℕ) layers_06_00_01_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_00_01_03

theorem valid_06_00_01_03 :
    SparseRowValid (![6, 6, 7, 10] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_06_00_01_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 6, 7, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 6 + 6 + 7 + 10 = 29
      decide
    have hzsq : (∑ i, (((![6, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 221
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_00_01_03
#print axioms Paper7MomentGapNumeric.valid_06_00_01_03

def qvalues_06_00_01_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 156, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_00_01_03

theorem row_06_00_01_03 : b4RowContribution (![6, 6, 7, 10] : Fin 4 → ℕ) = 156 := by
  calc
    b4RowContribution (![6, 6, 7, 10] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_06_00_01_03) :=
      sparseRow_sound (![6, 6, 7, 10] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_06_00_01_03) valid_06_00_01_03
    _ = 156 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_00_01_03 Q := by
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
        _ = 156 := by decide
#print axioms Paper7MomentGapNumeric.row_06_00_01_03

theorem weighted_06_00_01_03 : b4RawGapContribution ![6, 0, 1, 3] = 1872 := by
  calc
    b4RawGapContribution ![6, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 156 :=
      b4GapContribution_from_row 6 0 1 3 156 row_06_00_01_03
    _ = 1872 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_03

theorem row_06_00_01_04 : b4RowContribution (![6, 6, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 11 = 30
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_04

theorem weighted_06_00_01_04 : b4RawGapContribution ![6, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 6 0 1 4 0 row_06_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_04

theorem row_06_00_01_05 : b4RowContribution (![6, 6, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 12 = 31
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_05

theorem weighted_06_00_01_05 : b4RawGapContribution ![6, 0, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 0 :=
      b4GapContribution_from_row 6 0 1 5 0 row_06_00_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_05

theorem row_06_00_01_06 : b4RowContribution (![6, 6, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 13 = 32
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_06

theorem weighted_06_00_01_06 : b4RawGapContribution ![6, 0, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 0 :=
      b4GapContribution_from_row 6 0 1 6 0 row_06_00_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_06

theorem row_06_00_01_07 : b4RowContribution (![6, 6, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 14 = 33
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 317 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 317
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_07

theorem weighted_06_00_01_07 : b4RawGapContribution ![6, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 6 0 1 7 0 row_06_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_07

theorem row_06_00_01_08 : b4RowContribution (![6, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 15 = 34
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_08

theorem weighted_06_00_01_08 : b4RawGapContribution ![6, 0, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 8] = b4GapPatternWeight 0 1 8 * 0 :=
      b4GapContribution_from_row 6 0 1 8 0 row_06_00_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_08

theorem row_06_00_01_09 : b4RowContribution (![6, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 16 = 35
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_09

theorem weighted_06_00_01_09 : b4RawGapContribution ![6, 0, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 9] = b4GapPatternWeight 0 1 9 * 0 :=
      b4GapContribution_from_row 6 0 1 9 0 row_06_00_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_09

theorem row_06_00_01_10 : b4RowContribution (![6, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 17 = 36
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_10

theorem weighted_06_00_01_10 : b4RawGapContribution ![6, 0, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 10] = b4GapPatternWeight 0 1 10 * 0 :=
      b4GapContribution_from_row 6 0 1 10 0 row_06_00_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_10

theorem row_06_00_01_11 : b4RowContribution (![6, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 7, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 7 + 18 = 37
    decide
  have hzsq : (∑ i, (((![6, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_01_11

theorem weighted_06_00_01_11 : b4RawGapContribution ![6, 0, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 1, 11] = b4GapPatternWeight 0 1 11 * 0 :=
      b4GapContribution_from_row 6 0 1 11 0 row_06_00_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_01_11

def dvalues_06_00_01 : Fin 12 → ℕ := ![0, 0, 0, 1872, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_00_01

theorem dblock_06_00_01 : b4GapPatternDBlock 6 0 1 = 1872 := by
  calc
    b4GapPatternDBlock 6 0 1 = ∑ d : Fin 12, dvalues_06_00_01 d := by
      apply b4GapDBlock_of_rows 6 0 1 dvalues_06_00_01
      intro d
      fin_cases d
      · exact weighted_06_00_01_00
      · exact weighted_06_00_01_01
      · exact weighted_06_00_01_02
      · exact weighted_06_00_01_03
      · exact weighted_06_00_01_04
      · exact weighted_06_00_01_05
      · exact weighted_06_00_01_06
      · exact weighted_06_00_01_07
      · exact weighted_06_00_01_08
      · exact weighted_06_00_01_09
      · exact weighted_06_00_01_10
      · exact weighted_06_00_01_11
    _ = 1872 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_00_01

end Paper7MomentGapNumeric
