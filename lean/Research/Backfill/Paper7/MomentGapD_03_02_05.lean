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

def layers_03_02_05_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 24, 24, 24, 23, 21, 18, 14, 10, 6, 3, 1], ![1, 4, 10, 20, 34, 52, 73, 96, 120, 144, 168, 190, 208, 220, 224, 220, 208, 190, 168]]
#print axioms Paper7MomentGapNumeric.layers_03_02_05_00

theorem cells_03_02_05_00 : QTableValid (![3, 5, 10, 10] : Fin 4 → ℕ) layers_03_02_05_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_05_00

theorem valid_03_02_05_00 :
    SparseRowValid (![3, 5, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_05_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 10, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 10 + 10 = 28
      decide
    have hzsq : (∑ i, (((![3, 5, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 10^2 + 10^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_05_00
#print axioms Paper7MomentGapNumeric.valid_03_02_05_00

def qvalues_03_02_05_00 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_05_00

theorem row_03_02_05_00 : b4RowContribution (![3, 5, 10, 10] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![3, 5, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_03_02_05_00) :=
      sparseRow_sound (![3, 5, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_05_00) valid_03_02_05_00
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_05_00 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_05_00

theorem weighted_03_02_05_00 : b4RawGapContribution ![3, 2, 5, 0] = 240 := by
  calc
    b4RawGapContribution ![3, 2, 5, 0] = b4GapPatternWeight 2 5 0 * 20 :=
      b4GapContribution_from_row 3 2 5 0 20 row_03_02_05_00
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_00

theorem row_03_02_05_01 : b4RowContribution (![3, 5, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 11 = 29
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 11^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_01

theorem weighted_03_02_05_01 : b4RawGapContribution ![3, 2, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 1] = b4GapPatternWeight 2 5 1 * 0 :=
      b4GapContribution_from_row 3 2 5 1 0 row_03_02_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_01

def layers_03_02_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 24, 24, 24, 23, 21, 18, 14, 10, 6, 3, 1], ![1, 4, 10, 20, 34, 52, 73, 96, 120, 144, 168, 191, 212, 229, 240, 244, 240, 229, 212]]
#print axioms Paper7MomentGapNumeric.layers_03_02_05_02

theorem cells_03_02_05_02 : QTableValid (![3, 5, 10, 12] : Fin 4 → ℕ) layers_03_02_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_05_02

theorem valid_03_02_05_02 :
    SparseRowValid (![3, 5, 10, 12] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_02_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 10, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 10 + 12 = 30
      decide
    have hzsq : (∑ i, (((![3, 5, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 10^2 + 12^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_05_02
#print axioms Paper7MomentGapNumeric.valid_03_02_05_02

def qvalues_03_02_05_02 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_05_02

theorem row_03_02_05_02 : b4RowContribution (![3, 5, 10, 12] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![3, 5, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_03_02_05_02) :=
      sparseRow_sound (![3, 5, 10, 12] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_02_05_02) valid_03_02_05_02
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_05_02 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_05_02

theorem weighted_03_02_05_02 : b4RawGapContribution ![3, 2, 5, 2] = 240 := by
  calc
    b4RawGapContribution ![3, 2, 5, 2] = b4GapPatternWeight 2 5 2 * 10 :=
      b4GapContribution_from_row 3 2 5 2 10 row_03_02_05_02
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_02

theorem row_03_02_05_03 : b4RowContribution (![3, 5, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 13 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 13^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_03

theorem weighted_03_02_05_03 : b4RawGapContribution ![3, 2, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 3] = b4GapPatternWeight 2 5 3 * 0 :=
      b4GapContribution_from_row 3 2 5 3 0 row_03_02_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_03

theorem row_03_02_05_04 : b4RowContribution (![3, 5, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 14 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 14^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_04

theorem weighted_03_02_05_04 : b4RawGapContribution ![3, 2, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 4] = b4GapPatternWeight 2 5 4 * 0 :=
      b4GapContribution_from_row 3 2 5 4 0 row_03_02_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_04

theorem row_03_02_05_05 : b4RowContribution (![3, 5, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 15 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 359 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 15^2 = 359
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_05

theorem weighted_03_02_05_05 : b4RawGapContribution ![3, 2, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 5] = b4GapPatternWeight 2 5 5 * 0 :=
      b4GapContribution_from_row 3 2 5 5 0 row_03_02_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_05

theorem row_03_02_05_06 : b4RowContribution (![3, 5, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 16 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 16^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_06

theorem weighted_03_02_05_06 : b4RawGapContribution ![3, 2, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 6] = b4GapPatternWeight 2 5 6 * 0 :=
      b4GapContribution_from_row 3 2 5 6 0 row_03_02_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_06

theorem row_03_02_05_07 : b4RowContribution (![3, 5, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 17 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 17^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_07

theorem weighted_03_02_05_07 : b4RawGapContribution ![3, 2, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 7] = b4GapPatternWeight 2 5 7 * 0 :=
      b4GapContribution_from_row 3 2 5 7 0 row_03_02_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_07

theorem row_03_02_05_08 : b4RowContribution (![3, 5, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 18 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 18^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_08

theorem weighted_03_02_05_08 : b4RawGapContribution ![3, 2, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 8] = b4GapPatternWeight 2 5 8 * 0 :=
      b4GapContribution_from_row 3 2 5 8 0 row_03_02_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_08

theorem row_03_02_05_09 : b4RowContribution (![3, 5, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 10, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 10 + 19 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 10^2 + 19^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_05_09

theorem weighted_03_02_05_09 : b4RawGapContribution ![3, 2, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 5, 9] = b4GapPatternWeight 2 5 9 * 0 :=
      b4GapContribution_from_row 3 2 5 9 0 row_03_02_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_05_09

def dvalues_03_02_05 : Fin 10 → ℕ := ![240, 0, 240, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_05

theorem dblock_03_02_05 : b4GapPatternDBlock 3 2 5 = 480 := by
  calc
    b4GapPatternDBlock 3 2 5 = ∑ d : Fin 10, dvalues_03_02_05 d := by
      apply b4GapDBlock_of_rows 3 2 5 dvalues_03_02_05
      intro d
      fin_cases d
      · exact weighted_03_02_05_00
      · exact weighted_03_02_05_01
      · exact weighted_03_02_05_02
      · exact weighted_03_02_05_03
      · exact weighted_03_02_05_04
      · exact weighted_03_02_05_05
      · exact weighted_03_02_05_06
      · exact weighted_03_02_05_07
      · exact weighted_03_02_05_08
      · exact weighted_03_02_05_09
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_05

end Paper7MomentGapNumeric
