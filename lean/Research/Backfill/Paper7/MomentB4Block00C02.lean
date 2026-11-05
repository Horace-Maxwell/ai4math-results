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

theorem row_02_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 2, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 0] : Fin 4 → ℕ) i) = 2 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 0 = 2
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 4 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 0^2 = 4
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_00

theorem row_02_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 2, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 1] : Fin 4 → ℕ) i) = 3 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 1 = 3
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 5 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 1^2 = 5
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_01

theorem row_02_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 2, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 2] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 2 = 4
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 8 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 2^2 = 8
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_02

theorem row_02_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 2, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 3] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 3 = 5
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 13 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 3^2 = 13
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_03

theorem row_02_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 2, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 4] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 4 = 6
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 20 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 4^2 = 20
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_04

theorem row_02_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 2, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 5] : Fin 4 → ℕ) i) = 7 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 5 = 7
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 29 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 5^2 = 29
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_05

def layers_02_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_02_06

theorem cells_02_06 : QTableValid (![0, 0, 2, 6] : Fin 4 → ℕ) layers_02_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_02_06

theorem valid_02_06 :
    SparseRowValid (![0, 0, 2, 6] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 2, 6] : Fin 4 → ℕ) i) = 8 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 2 + 6 = 8
      decide
    have hzsq : (∑ i, (((![0, 0, 2, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 40 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 2^2 + 6^2 = 40
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06
#print axioms Paper7MomentBlock00.valid_02_06

def qvalues_02_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_02_06

theorem row_02_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩⟩) = 3 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 2, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 2, 6] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_06) :=
      sparseRow_sound (![0, 0, 2, 6] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_06) valid_02_06
    _ = 3 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06 Q := by
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
        _ = 3 := by decide
#print axioms Paper7MomentBlock00.row_02_06

theorem row_02_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 2, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 7] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 7 = 9
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 53 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 7^2 = 53
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_07

theorem row_02_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 2, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 8] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 8 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 68 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 8^2 = 68
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_08

theorem row_02_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 2, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 9] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 9 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 85 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 9^2 = 85
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_09

theorem row_02_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 2, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 10] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 10 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 104 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 10^2 = 104
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_10

theorem row_02_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 2, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 11] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 11 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 125 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 11^2 = 125
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_11

theorem row_02_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 2, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 12] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 12 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 12^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_12

def layers_02_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_02_13

theorem cells_02_13 : QTableValid (![0, 0, 2, 13] : Fin 4 → ℕ) layers_02_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_02_13

theorem valid_02_13 :
    SparseRowValid (![0, 0, 2, 13] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 2, 13] : Fin 4 → ℕ) i) = 15 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 2 + 13 = 15
      decide
    have hzsq : (∑ i, (((![0, 0, 2, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 173 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 2^2 + 13^2 = 173
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_13
#print axioms Paper7MomentBlock00.valid_02_13

def qvalues_02_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_02_13

theorem row_02_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨13, by decide⟩⟩) = 3 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 2, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 2, 13] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_02_13) :=
      sparseRow_sound (![0, 0, 2, 13] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_13) valid_02_13
    _ = 3 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_13 Q := by
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
        _ = 3 := by decide
#print axioms Paper7MomentBlock00.row_02_13

theorem row_02_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 2, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 14] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 14 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 200 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 14^2 = 200
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_14

def layers_02_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0]]
#print axioms Paper7MomentBlock00.layers_02_15

theorem cells_02_15 : QTableValid (![0, 0, 2, 15] : Fin 4 → ℕ) layers_02_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_02_15

theorem valid_02_15 :
    SparseRowValid (![0, 0, 2, 15] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_02_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 2, 15] : Fin 4 → ℕ) i) = 17 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 2 + 15 = 17
      decide
    have hzsq : (∑ i, (((![0, 0, 2, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 2^2 + 15^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_15
#print axioms Paper7MomentBlock00.valid_02_15

def qvalues_02_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_02_15

theorem row_02_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨15, by decide⟩⟩) = 5 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 2, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 2, 15] : Fin 4 → ℕ) =
        sparseRowValue ({10, 16} : Finset (Fin 19)) (fun _ => layers_02_15) :=
      sparseRow_sound (![0, 0, 2, 15] : Fin 4 → ℕ) ({10, 16} : Finset (Fin 19)) (fun _ => layers_02_15) valid_02_15
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_15 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 5 := by decide
#print axioms Paper7MomentBlock00.row_02_15

theorem row_02_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 2, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 16] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 16 = 18
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 16^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_16

def layers_02_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2]]
#print axioms Paper7MomentBlock00.layers_02_17

theorem cells_02_17 : QTableValid (![0, 0, 2, 17] : Fin 4 → ℕ) layers_02_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_02_17

theorem valid_02_17 :
    SparseRowValid (![0, 0, 2, 17] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_02_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 2, 17] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 2 + 17 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 2, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 2^2 + 17^2 = 293
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_17
#print axioms Paper7MomentBlock00.valid_02_17

def qvalues_02_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0]
#print axioms Paper7MomentBlock00.qvalues_02_17

theorem row_02_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨17, by decide⟩⟩) = 6 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 2, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 2, 17] : Fin 4 → ℕ) =
        sparseRowValue ({11, 17} : Finset (Fin 19)) (fun _ => layers_02_17) :=
      sparseRow_sound (![0, 0, 2, 17] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_02_17) valid_02_17
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_17 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 6 := by decide
#print axioms Paper7MomentBlock00.row_02_17

theorem row_02_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 2, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 18] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 18 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 18^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_18

theorem row_02_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 2, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 19] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 19 = 21
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 19^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_19

theorem row_02_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 2, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 20] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 20 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 20^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_20

theorem row_02_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 2, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 21] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 21 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 21^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_21

theorem row_02_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 2, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 22] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 22 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 488 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 22^2 = 488
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_22

theorem row_02_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 2, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 23] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 23 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 533 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 23^2 = 533
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_23

theorem row_02_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 2, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 24] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 24 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 580 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 24^2 = 580
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_24

theorem row_02_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 2, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 25] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 25 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 629 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 25^2 = 629
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_25

theorem row_02_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 2, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 26] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 26 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 680 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 26^2 = 680
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_26

theorem row_02_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 2, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 27] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 27 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 733 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 27^2 = 733
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_27

theorem row_02_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 2, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 28] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 28 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 788 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 28^2 = 788
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_28

theorem row_02_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 2, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 29] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 29 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 845 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 29^2 = 845
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_29

theorem row_02_30 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨30, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨30, by decide⟩⟩) = (![0, 0, 2, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 30] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 30 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 904 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 30^2 = 904
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_30

theorem row_02_31 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨31, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨31, by decide⟩⟩) = (![0, 0, 2, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 31] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 31 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 965 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 31^2 = 965
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_31

theorem row_02_32 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨32, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨32, by decide⟩⟩) = (![0, 0, 2, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 32] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 32 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1028 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 32^2 = 1028
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_32

theorem row_02_33 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨33, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨33, by decide⟩⟩) = (![0, 0, 2, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 33] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 33 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1093 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 33^2 = 1093
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_33

theorem row_02_34 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨34, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨34, by decide⟩⟩) = (![0, 0, 2, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 34] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 34 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1160 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 34^2 = 1160
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_34

theorem row_02_35 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨35, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨35, by decide⟩⟩) = (![0, 0, 2, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 2, 35] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 2 + 35 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 2, 35] : Fin 4 → ℕ) i : ℤ)^2)) = 1229 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 2^2 + 35^2 = 1229
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_02_35

def values_02 : Fin 36 → ℕ := ![0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 5, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_02

theorem column_02 :
    (∑ d : Fin 36, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, d⟩)) = 17 := by
  calc
    (∑ d : Fin 36, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, d⟩)) =
        ∑ d : Fin 36, values_02 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_02_00
      · exact row_02_01
      · exact row_02_02
      · exact row_02_03
      · exact row_02_04
      · exact row_02_05
      · exact row_02_06
      · exact row_02_07
      · exact row_02_08
      · exact row_02_09
      · exact row_02_10
      · exact row_02_11
      · exact row_02_12
      · exact row_02_13
      · exact row_02_14
      · exact row_02_15
      · exact row_02_16
      · exact row_02_17
      · exact row_02_18
      · exact row_02_19
      · exact row_02_20
      · exact row_02_21
      · exact row_02_22
      · exact row_02_23
      · exact row_02_24
      · exact row_02_25
      · exact row_02_26
      · exact row_02_27
      · exact row_02_28
      · exact row_02_29
      · exact row_02_30
      · exact row_02_31
      · exact row_02_32
      · exact row_02_33
      · exact row_02_34
      · exact row_02_35
    _ = 17 := by decide
#print axioms Paper7MomentBlock00.column_02

end Paper7MomentBlock00
