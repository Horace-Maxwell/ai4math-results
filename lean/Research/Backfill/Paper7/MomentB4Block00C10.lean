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

theorem row_10_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 10, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 0] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 0 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 0^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_00

theorem row_10_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 10, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 1] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 1 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 101 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 1^2 = 101
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_01

theorem row_10_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 10, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 2] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 2 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 104 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 2^2 = 104
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_02

theorem row_10_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 10, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 3] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 3 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 3^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_03

theorem row_10_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 10, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 4] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 4 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 116 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 4^2 = 116
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_04

theorem row_10_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 10, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 5] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 5 = 15
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 125 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 5^2 = 125
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_05

theorem row_10_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨6, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 10, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 6 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 136 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 6^2 = 136
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_06

theorem row_10_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 10, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 7 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 7^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_07

def layers_10_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 8, 7, 6, 5, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_10_08

theorem cells_10_08 : QTableValid (![0, 0, 10, 8] : Fin 4 → ℕ) layers_10_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_10_08

theorem valid_10_08 :
    SparseRowValid (![0, 0, 10, 8] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_10_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 10, 8] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 10 + 8 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 10, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 10^2 + 8^2 = 164
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_10_08
#print axioms Paper7MomentBlock00.valid_10_08

def qvalues_10_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]
#print axioms Paper7MomentBlock00.qvalues_10_08

theorem row_10_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨8, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 10, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 10, 8] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_10_08) :=
      sparseRow_sound (![0, 0, 10, 8] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_10_08) valid_10_08
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_10_08 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_10_08

def layers_10_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 9, 8, 7, 6, 5, 4, 3, 2]]
#print axioms Paper7MomentBlock00.layers_10_09

theorem cells_10_09 : QTableValid (![0, 0, 10, 9] : Fin 4 → ℕ) layers_10_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_10_09

theorem valid_10_09 :
    SparseRowValid (![0, 0, 10, 9] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_10_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 10, 9] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 10 + 9 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 10, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 181 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 10^2 + 9^2 = 181
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_10_09
#print axioms Paper7MomentBlock00.valid_10_09

def qvalues_10_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_10_09

theorem row_10_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨9, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 10, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 10, 9] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_10_09) :=
      sparseRow_sound (![0, 0, 10, 9] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_10_09) valid_10_09
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_10_09 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentBlock00.row_10_09

theorem row_10_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 10, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 10 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 200 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 10^2 = 200
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_10

def layers_10_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 10, 9, 8, 7, 6, 5, 4]]
#print axioms Paper7MomentBlock00.layers_10_11

theorem cells_10_11 : QTableValid (![0, 0, 10, 11] : Fin 4 → ℕ) layers_10_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_10_11

theorem valid_10_11 :
    SparseRowValid (![0, 0, 10, 11] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_10_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 10, 11] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 10 + 11 = 21
      decide
    have hzsq : (∑ i, (((![0, 0, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 10^2 + 11^2 = 221
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_10_11
#print axioms Paper7MomentBlock00.valid_10_11

def qvalues_10_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_10_11

theorem row_10_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩⟩) = 17 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 10, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({8, 14} : Finset (Fin 19)) (fun _ => layers_10_11) :=
      sparseRow_sound (![0, 0, 10, 11] : Fin 4 → ℕ) ({8, 14} : Finset (Fin 19)) (fun _ => layers_10_11) valid_10_11
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_10_11 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 17 := by decide
#print axioms Paper7MomentBlock00.row_10_11

def layers_10_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 11, 10, 9, 8, 7, 6, 5]]
#print axioms Paper7MomentBlock00.layers_10_12

theorem cells_10_12 : QTableValid (![0, 0, 10, 12] : Fin 4 → ℕ) layers_10_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_10_12

theorem valid_10_12 :
    SparseRowValid (![0, 0, 10, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_10_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 10, 12] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 10 + 12 = 22
      decide
    have hzsq : (∑ i, (((![0, 0, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 10^2 + 12^2 = 244
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_10_12
#print axioms Paper7MomentBlock00.valid_10_12

def qvalues_10_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_10_12

theorem row_10_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 10, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_10_12) :=
      sparseRow_sound (![0, 0, 10, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_10_12) valid_10_12
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_10_12 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentBlock00.row_10_12

theorem row_10_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 10, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 13 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 13^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_13

theorem row_10_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 10, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 14] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 14 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 296 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 14^2 = 296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_14

theorem row_10_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 10, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 15 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 15^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_15

theorem row_10_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 10, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 16 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 16^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_16

theorem row_10_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 10, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 17 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 17^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_17

theorem row_10_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 10, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 18 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 424 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 18^2 = 424
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_18

theorem row_10_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 10, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 19 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 19^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_19

theorem row_10_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 10, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 20 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 500 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 20^2 = 500
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_20

theorem row_10_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 10, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 21 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 541 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 21^2 = 541
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_21

theorem row_10_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 10, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 22 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 584 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 22^2 = 584
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_22

theorem row_10_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 10, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 23 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 629 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 23^2 = 629
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_23

theorem row_10_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 10, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 24 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 676 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 24^2 = 676
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_24

theorem row_10_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 10, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 25 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 725 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 25^2 = 725
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_25

theorem row_10_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 10, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 26 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 776 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 26^2 = 776
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_26

theorem row_10_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 10, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 10, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 10 + 27 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 10, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 829 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 10^2 + 27^2 = 829
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_10_27

def values_10 : Fin 28 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0, 17, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_10

theorem column_10 :
    (∑ d : Fin 28, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, d⟩)) = 35 := by
  calc
    (∑ d : Fin 28, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨10, by decide⟩, d⟩)) =
        ∑ d : Fin 28, values_10 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_10_00
      · exact row_10_01
      · exact row_10_02
      · exact row_10_03
      · exact row_10_04
      · exact row_10_05
      · exact row_10_06
      · exact row_10_07
      · exact row_10_08
      · exact row_10_09
      · exact row_10_10
      · exact row_10_11
      · exact row_10_12
      · exact row_10_13
      · exact row_10_14
      · exact row_10_15
      · exact row_10_16
      · exact row_10_17
      · exact row_10_18
      · exact row_10_19
      · exact row_10_20
      · exact row_10_21
      · exact row_10_22
      · exact row_10_23
      · exact row_10_24
      · exact row_10_25
      · exact row_10_26
      · exact row_10_27
    _ = 35 := by decide
#print axioms Paper7MomentBlock00.column_10

end Paper7MomentBlock00
