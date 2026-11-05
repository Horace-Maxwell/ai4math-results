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

theorem row_00_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 0, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 0] : Fin 4 → ℕ) i) = 0 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 0 = 0
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 0 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 0^2 = 0
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_00

theorem row_00_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 0, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 1] : Fin 4 → ℕ) i) = 1 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 1 = 1
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 1 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 1^2 = 1
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_01

theorem row_00_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 0, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 2] : Fin 4 → ℕ) i) = 2 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 2 = 2
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 4 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 2^2 = 4
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_02

theorem row_00_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 0, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 3] : Fin 4 → ℕ) i) = 3 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 3 = 3
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 9 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 3^2 = 9
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_03

theorem row_00_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 0, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 4] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 4 = 4
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 16 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 4^2 = 16
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_04

theorem row_00_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 0, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 5] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 5 = 5
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 25 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 5^2 = 25
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_05

theorem row_00_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨6, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 0, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 6] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 6 = 6
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 36 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 6^2 = 36
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_06

def layers_00_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_00_07

theorem cells_00_07 : QTableValid (![0, 0, 0, 7] : Fin 4 → ℕ) layers_00_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_07

theorem valid_00_07 :
    SparseRowValid (![0, 0, 0, 7] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 7] : Fin 4 → ℕ) i) = 7 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 7 = 7
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 49 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 7^2 = 49
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07
#print axioms Paper7MomentBlock00.valid_00_07

def qvalues_00_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_07

theorem row_00_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 0, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 7] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_07) :=
      sparseRow_sound (![0, 0, 0, 7] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_07) valid_00_07
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_00_07

theorem row_00_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 0, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 8] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 8 = 8
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 64 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 8^2 = 64
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_08

theorem row_00_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 0, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 9] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 9 = 9
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 9^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_09

theorem row_00_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 0, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 10] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 10 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 10^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_10

theorem row_00_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 0, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 11] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 11 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 121 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 11^2 = 121
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_11

theorem row_00_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 0, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 12] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 12 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 144 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 12^2 = 144
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_12

theorem row_00_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨13, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 0, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 13] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 13 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 13^2 = 169
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_13

def layers_00_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_00_14

theorem cells_00_14 : QTableValid (![0, 0, 0, 14] : Fin 4 → ℕ) layers_00_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_14

theorem valid_00_14 :
    SparseRowValid (![0, 0, 0, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 14] : Fin 4 → ℕ) i) = 14 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 14 = 14
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 14^2 = 196
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_14
#print axioms Paper7MomentBlock00.valid_00_14

def qvalues_00_14 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_14

theorem row_00_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 0, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_14) :=
      sparseRow_sound (![0, 0, 0, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_14) valid_00_14
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_14 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_00_14

def layers_00_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_00_15

theorem cells_00_15 : QTableValid (![0, 0, 0, 15] : Fin 4 → ℕ) layers_00_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_15

theorem valid_00_15 :
    SparseRowValid (![0, 0, 0, 15] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 15] : Fin 4 → ℕ) i) = 15 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 15 = 15
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 15^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_15
#print axioms Paper7MomentBlock00.valid_00_15

def qvalues_00_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_15

theorem row_00_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨15, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 0, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 15] : Fin 4 → ℕ) =
        sparseRowValue ({15} : Finset (Fin 19)) (fun _ => layers_00_15) :=
      sparseRow_sound (![0, 0, 0, 15] : Fin 4 → ℕ) ({15} : Finset (Fin 19)) (fun _ => layers_00_15) valid_00_15
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_15 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_00_15

theorem row_00_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 0, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 16] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 16 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 256 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 16^2 = 256
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_16

def layers_00_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]]
#print axioms Paper7MomentBlock00.layers_00_17

theorem cells_00_17 : QTableValid (![0, 0, 0, 17] : Fin 4 → ℕ) layers_00_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_17

theorem valid_00_17 :
    SparseRowValid (![0, 0, 0, 17] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_00_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 17] : Fin 4 → ℕ) i) = 17 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 17 = 17
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 17^2 = 289
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_17
#print axioms Paper7MomentBlock00.valid_00_17

def qvalues_00_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_17

theorem row_00_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨17, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 0, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 17] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_00_17) :=
      sparseRow_sound (![0, 0, 0, 17] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_00_17) valid_00_17
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_17 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_00_17

theorem row_00_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 0, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 18] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 18 = 18
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 18^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_18

theorem row_00_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 0, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 19] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 19 = 19
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 19^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_19

theorem row_00_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 0, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 20] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 20 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 20^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_20

theorem row_00_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 0, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 21] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 21 = 21
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 21^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_21

theorem row_00_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 0, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 22] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 22 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 484 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 22^2 = 484
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_22

def layers_00_23 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]
#print axioms Paper7MomentBlock00.layers_00_23

theorem cells_00_23 : QTableValid (![0, 0, 0, 23] : Fin 4 → ℕ) layers_00_23 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_23

theorem valid_00_23 :
    SparseRowValid (![0, 0, 0, 23] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_23) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 23] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 23 = 23
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 23^2 = 529
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_23
#print axioms Paper7MomentBlock00.valid_00_23

def qvalues_00_23 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_23

theorem row_00_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨23, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 0, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 23] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_23) :=
      sparseRow_sound (![0, 0, 0, 23] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_23) valid_00_23
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_23 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_00_23

def layers_00_24 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]
#print axioms Paper7MomentBlock00.layers_00_24

theorem cells_00_24 : QTableValid (![0, 0, 0, 24] : Fin 4 → ℕ) layers_00_24 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_00_24

theorem valid_00_24 :
    SparseRowValid (![0, 0, 0, 24] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_24) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 0, 24] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 0 + 24 = 24
      decide
    have hzsq : (∑ i, (((![0, 0, 0, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 576 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 0^2 + 24^2 = 576
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_24
#print axioms Paper7MomentBlock00.valid_00_24

def qvalues_00_24 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_00_24

theorem row_00_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨24, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 0, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 0, 24] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_24) :=
      sparseRow_sound (![0, 0, 0, 24] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_24) valid_00_24
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_24 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_00_24

theorem row_00_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 0, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 25] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 25 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 625 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 25^2 = 625
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_25

theorem row_00_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 0, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 26] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 26 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 676 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 26^2 = 676
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_26

theorem row_00_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 0, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 27] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 27 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 729 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 27^2 = 729
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_27

theorem row_00_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 0, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 28] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 28 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 784 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 28^2 = 784
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_28

theorem row_00_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 0, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 29] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 29 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 841 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 29^2 = 841
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_29

theorem row_00_30 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨30, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨30, by decide⟩⟩) = (![0, 0, 0, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 30] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 30 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 900 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 30^2 = 900
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_30

theorem row_00_31 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨31, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨31, by decide⟩⟩) = (![0, 0, 0, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 31] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 31 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 961 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 31^2 = 961
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_31

theorem row_00_32 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨32, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨32, by decide⟩⟩) = (![0, 0, 0, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 32] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 32 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1024 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 32^2 = 1024
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_32

theorem row_00_33 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨33, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨33, by decide⟩⟩) = (![0, 0, 0, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 33] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 33 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1089 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 33^2 = 1089
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_33

theorem row_00_34 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨34, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨34, by decide⟩⟩) = (![0, 0, 0, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 34] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 34 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1156 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 34^2 = 1156
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_34

theorem row_00_35 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨35, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨35, by decide⟩⟩) = (![0, 0, 0, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 35] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 35 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 35] : Fin 4 → ℕ) i : ℤ)^2)) = 1225 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 35^2 = 1225
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_35

theorem row_00_36 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨36, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨36, by decide⟩⟩) = (![0, 0, 0, 36] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 36] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 36 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 36] : Fin 4 → ℕ) i : ℤ)^2)) = 1296 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 36^2 = 1296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_36

theorem row_00_37 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨37, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨37, by decide⟩⟩) = (![0, 0, 0, 37] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 0, 37] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 0 + 37 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 0, 37] : Fin 4 → ℕ) i : ℤ)^2)) = 1369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 0^2 + 37^2 = 1369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_00_37

def values_00 : Fin 38 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_00

theorem column_00 :
    (∑ d : Fin 38, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, d⟩)) = 7 := by
  calc
    (∑ d : Fin 38, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, d⟩)) =
        ∑ d : Fin 38, values_00 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_00_00
      · exact row_00_01
      · exact row_00_02
      · exact row_00_03
      · exact row_00_04
      · exact row_00_05
      · exact row_00_06
      · exact row_00_07
      · exact row_00_08
      · exact row_00_09
      · exact row_00_10
      · exact row_00_11
      · exact row_00_12
      · exact row_00_13
      · exact row_00_14
      · exact row_00_15
      · exact row_00_16
      · exact row_00_17
      · exact row_00_18
      · exact row_00_19
      · exact row_00_20
      · exact row_00_21
      · exact row_00_22
      · exact row_00_23
      · exact row_00_24
      · exact row_00_25
      · exact row_00_26
      · exact row_00_27
      · exact row_00_28
      · exact row_00_29
      · exact row_00_30
      · exact row_00_31
      · exact row_00_32
      · exact row_00_33
      · exact row_00_34
      · exact row_00_35
      · exact row_00_36
      · exact row_00_37
    _ = 7 := by decide
#print axioms Paper7MomentBlock00.column_00

end Paper7MomentBlock00
