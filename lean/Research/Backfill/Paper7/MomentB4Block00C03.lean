import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4PrefixBlocks

/-! Generated UNTRUSTED proof-source candidate for the complete B4 prefix (0,0).
No native candidate flag, declared count, or data-file coverage is a hypothesis.
Each finite row/DP-cell proof must be accepted by the Lean kernel. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentBlock00
open Paper7MomentCertificate Paper7MomentCounts Paper7MomentDP
open scoped BigOperators

theorem row_03_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 3, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 0] : Fin 4 → ℕ) i) = 3 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 0 = 3
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 9 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 0^2 = 9
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_00

theorem row_03_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 3, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 1] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 1 = 4
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 10 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 1^2 = 10
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_01

theorem row_03_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 3, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 2] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 2 = 5
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 13 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 2^2 = 13
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_02

theorem row_03_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 3, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 3] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 3 = 6
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 18 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 3^2 = 18
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_03

theorem row_03_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 3, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 4] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 4 = 7
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 25 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 4^2 = 25
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_04

def layers_03_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_03_05

theorem cells_03_05 : QTableValid (![0, 0, 3, 5] : Fin 4 → ℕ) layers_03_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_03_05

theorem valid_03_05 :
    SparseRowValid (![0, 0, 3, 5] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 3, 5] : Fin 4 → ℕ) i) = 8 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 3 + 5 = 8
      decide
    have hzsq : (∑ i, (((![0, 0, 3, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 34 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 3^2 + 5^2 = 34
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_05
#print axioms Paper7MomentBlock00.valid_03_05

def qvalues_03_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_03_05

theorem row_03_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 3, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 3, 5] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_03_05) :=
      sparseRow_sound (![0, 0, 3, 5] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_05) valid_03_05
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_05 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_03_05

def layers_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_03_06

theorem cells_03_06 : QTableValid (![0, 0, 3, 6] : Fin 4 → ℕ) layers_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_03_06

theorem valid_03_06 :
    SparseRowValid (![0, 0, 3, 6] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 3, 6] : Fin 4 → ℕ) i) = 9 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 3 + 6 = 9
      decide
    have hzsq : (∑ i, (((![0, 0, 3, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 45 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 3^2 + 6^2 = 45
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_06
#print axioms Paper7MomentBlock00.valid_03_06

def qvalues_03_06 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_03_06

theorem row_03_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩⟩) = 5 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 3, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 3, 6] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_06) :=
      sparseRow_sound (![0, 0, 3, 6] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_06) valid_03_06
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_06 Q := by
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
        _ = 5 := by decide
#print axioms Paper7MomentBlock00.row_03_06

theorem row_03_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 3, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 7] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 7 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 7^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_07

theorem row_03_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 3, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 8] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 8 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 8^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_08

theorem row_03_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 3, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 9] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 9 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 90 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 9^2 = 90
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_09

theorem row_03_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 3, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 10] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 10 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 10^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_10

theorem row_03_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 3, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 11] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 11 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 11^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_11

theorem row_03_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 3, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 12] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 12 = 15
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 12^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_12

def layers_03_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0]]
#print axioms Paper7MomentBlock00.layers_03_13

theorem cells_03_13 : QTableValid (![0, 0, 3, 13] : Fin 4 → ℕ) layers_03_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_03_13

theorem valid_03_13 :
    SparseRowValid (![0, 0, 3, 13] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_03_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 3, 13] : Fin 4 → ℕ) i) = 16 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 3 + 13 = 16
      decide
    have hzsq : (∑ i, (((![0, 0, 3, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 3^2 + 13^2 = 178
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_13
#print axioms Paper7MomentBlock00.valid_03_13

def qvalues_03_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_03_13

theorem row_03_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨13, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 3, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 3, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_03_13) :=
      sparseRow_sound (![0, 0, 3, 13] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_03_13) valid_03_13
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_13 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentBlock00.row_03_13

theorem row_03_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 3, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 14] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 14 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 14^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_14

def layers_03_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_03_15

theorem cells_03_15 : QTableValid (![0, 0, 3, 15] : Fin 4 → ℕ) layers_03_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_03_15

theorem valid_03_15 :
    SparseRowValid (![0, 0, 3, 15] : Fin 4 → ℕ) ({6, 12, 18} : Finset (Fin 19)) (fun _ => layers_03_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 3, 15] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 3 + 15 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 3, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 3^2 + 15^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_15
#print axioms Paper7MomentBlock00.valid_03_15

def qvalues_03_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1]
#print axioms Paper7MomentBlock00.qvalues_03_15

theorem row_03_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩⟩) = 9 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 3, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 3, 15] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12, 18} : Finset (Fin 19)) (fun _ => layers_03_15) :=
      sparseRow_sound (![0, 0, 3, 15] : Fin 4 → ℕ) ({6, 12, 18} : Finset (Fin 19)) (fun _ => layers_03_15) valid_03_15
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_15 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
        _ = 9 := by decide
#print axioms Paper7MomentBlock00.row_03_15

theorem row_03_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 3, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 16] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 16 = 19
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 16^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_16

theorem row_03_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 3, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 17] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 17 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 17^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_17

theorem row_03_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 3, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 18] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 18 = 21
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 18^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_18

theorem row_03_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 3, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 19] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 19 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 19^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_19

theorem row_03_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 3, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 20] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 20 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 20^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_20

theorem row_03_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 3, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 21] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 21 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 21^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_21

theorem row_03_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 3, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 22] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 22 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 22^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_22

theorem row_03_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 3, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 23] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 23 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 538 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 23^2 = 538
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_23

theorem row_03_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 3, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 24] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 24 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 24^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_24

theorem row_03_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 3, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 25] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 25 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 634 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 25^2 = 634
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_25

theorem row_03_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 3, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 26] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 26 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 685 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 26^2 = 685
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_26

theorem row_03_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 3, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 27] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 27 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 738 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 27^2 = 738
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_27

theorem row_03_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 3, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 28] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 28 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 793 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 28^2 = 793
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_28

theorem row_03_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 3, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 29] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 29 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 850 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 29^2 = 850
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_29

theorem row_03_30 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨30, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨30, by decide⟩⟩) = (![0, 0, 3, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 30] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 30 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 909 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 30^2 = 909
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_30

theorem row_03_31 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨31, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨31, by decide⟩⟩) = (![0, 0, 3, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 31] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 31 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 970 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 31^2 = 970
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_31

theorem row_03_32 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨32, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨32, by decide⟩⟩) = (![0, 0, 3, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 32] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 32 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1033 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 32^2 = 1033
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_32

theorem row_03_33 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨33, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨33, by decide⟩⟩) = (![0, 0, 3, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 33] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 33 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1098 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 33^2 = 1098
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_33

theorem row_03_34 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨34, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨34, by decide⟩⟩) = (![0, 0, 3, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 3, 34] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 3 + 34 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 3, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1165 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 3^2 + 34^2 = 1165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_03_34

def values_03 : Fin 35 → ℕ := ![0, 0, 0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 8, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_03

theorem column_03 :
    (∑ d : Fin 35, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, d⟩)) = 24 := by
  calc
    (∑ d : Fin 35, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, d⟩)) =
        ∑ d : Fin 35, values_03 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_03_00
      · exact row_03_01
      · exact row_03_02
      · exact row_03_03
      · exact row_03_04
      · exact row_03_05
      · exact row_03_06
      · exact row_03_07
      · exact row_03_08
      · exact row_03_09
      · exact row_03_10
      · exact row_03_11
      · exact row_03_12
      · exact row_03_13
      · exact row_03_14
      · exact row_03_15
      · exact row_03_16
      · exact row_03_17
      · exact row_03_18
      · exact row_03_19
      · exact row_03_20
      · exact row_03_21
      · exact row_03_22
      · exact row_03_23
      · exact row_03_24
      · exact row_03_25
      · exact row_03_26
      · exact row_03_27
      · exact row_03_28
      · exact row_03_29
      · exact row_03_30
      · exact row_03_31
      · exact row_03_32
      · exact row_03_33
      · exact row_03_34
    _ = 24 := by decide
#print axioms Paper7MomentBlock00.column_03

end Paper7MomentBlock00
