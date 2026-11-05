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

theorem row_12_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 12, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 0] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 0 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 144 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 0^2 = 144
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_00

theorem row_12_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 12, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 1] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 1 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 1^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_01

theorem row_12_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 12, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 2] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 2 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 2^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_02

theorem row_12_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 12, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 3] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 3 = 15
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 3^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_03

def layers_12_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0]]
#print axioms Paper7MomentBlock00.layers_12_04

theorem cells_12_04 : QTableValid (![0, 0, 12, 4] : Fin 4 → ℕ) layers_12_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_04

theorem valid_12_04 :
    SparseRowValid (![0, 0, 12, 4] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 4] : Fin 4 → ℕ) i) = 16 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 4 = 16
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 160 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 4^2 = 160
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_04
#print axioms Paper7MomentBlock00.valid_12_04

def qvalues_12_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_04

theorem row_12_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨4, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 12, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 4] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_12_04) :=
      sparseRow_sound (![0, 0, 12, 4] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_04) valid_12_04
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_04 Q := by
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
#print axioms Paper7MomentBlock00.row_12_04

def layers_12_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0]]
#print axioms Paper7MomentBlock00.layers_12_05

theorem cells_12_05 : QTableValid (![0, 0, 12, 5] : Fin 4 → ℕ) layers_12_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_05

theorem valid_12_05 :
    SparseRowValid (![0, 0, 12, 5] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 5] : Fin 4 → ℕ) i) = 17 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 5 = 17
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 5^2 = 169
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_05
#print axioms Paper7MomentBlock00.valid_12_05

def qvalues_12_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_05

theorem row_12_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨5, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 12, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 5] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_12_05) :=
      sparseRow_sound (![0, 0, 12, 5] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_05) valid_12_05
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_05 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_12_05

def layers_12_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_12_06

theorem cells_12_06 : QTableValid (![0, 0, 12, 6] : Fin 4 → ℕ) layers_12_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_06

theorem valid_12_06 :
    SparseRowValid (![0, 0, 12, 6] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_12_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 6] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 6 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 6^2 = 180
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_06
#print axioms Paper7MomentBlock00.valid_12_06

def qvalues_12_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_06

theorem row_12_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨6, by decide⟩⟩) = 7 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 12, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 6] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_12_06) :=
      sparseRow_sound (![0, 0, 12, 6] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_12_06) valid_12_06
    _ = 7 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_06 Q := by
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
        _ = 7 := by decide
#print axioms Paper7MomentBlock00.row_12_06

def layers_12_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3, 2]]
#print axioms Paper7MomentBlock00.layers_12_07

theorem cells_12_07 : QTableValid (![0, 0, 12, 7] : Fin 4 → ℕ) layers_12_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_07

theorem valid_12_07 :
    SparseRowValid (![0, 0, 12, 7] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_12_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 7] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 7 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 7^2 = 193
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_07
#print axioms Paper7MomentBlock00.valid_12_07

def qvalues_12_07 : Fin 19 → ℕ := ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_07

theorem row_12_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨7, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 12, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 7] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_12_07) :=
      sparseRow_sound (![0, 0, 12, 7] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_12_07) valid_12_07
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_07 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_12_07

def layers_12_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3]]
#print axioms Paper7MomentBlock00.layers_12_08

theorem cells_12_08 : QTableValid (![0, 0, 12, 8] : Fin 4 → ℕ) layers_12_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_08

theorem valid_12_08 :
    SparseRowValid (![0, 0, 12, 8] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 8] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 8 = 20
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 208 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 8^2 = 208
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_08
#print axioms Paper7MomentBlock00.valid_12_08

def qvalues_12_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_08

theorem row_12_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨8, by decide⟩⟩) = 5 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 12, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 8] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_12_08) :=
      sparseRow_sound (![0, 0, 12, 8] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_12_08) valid_12_08
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_08 Q := by
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
        _ = 5 := by decide
#print axioms Paper7MomentBlock00.row_12_08

def layers_12_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 9, 8, 7, 6, 5, 4]]
#print axioms Paper7MomentBlock00.layers_12_09

theorem cells_12_09 : QTableValid (![0, 0, 12, 9] : Fin 4 → ℕ) layers_12_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_09

theorem valid_12_09 :
    SparseRowValid (![0, 0, 12, 9] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 9] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 9 = 21
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 9^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_09
#print axioms Paper7MomentBlock00.valid_12_09

def qvalues_12_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_09

theorem row_12_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩⟩) = 17 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 12, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 9] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_09) :=
      sparseRow_sound (![0, 0, 12, 9] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_09) valid_12_09
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_09 Q := by
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
        _ = 17 := by decide
#print axioms Paper7MomentBlock00.row_12_09

def layers_12_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 11, 10, 9, 8, 7, 6, 5]]
#print axioms Paper7MomentBlock00.layers_12_10

theorem cells_12_10 : QTableValid (![0, 0, 12, 10] : Fin 4 → ℕ) layers_12_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_10

theorem valid_12_10 :
    SparseRowValid (![0, 0, 12, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_12_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 10] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 10 = 22
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 10^2 = 244
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_10
#print axioms Paper7MomentBlock00.valid_12_10

def qvalues_12_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_10

theorem row_12_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨10, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 12, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 10] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_12_10) :=
      sparseRow_sound (![0, 0, 12, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_12_10) valid_12_10
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_10 Q := by
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
#print axioms Paper7MomentBlock00.row_12_10

theorem row_12_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 12, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 11 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 11^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_11

def layers_12_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 12, 11, 10, 9, 8, 7]]
#print axioms Paper7MomentBlock00.layers_12_12

theorem cells_12_12 : QTableValid (![0, 0, 12, 12] : Fin 4 → ℕ) layers_12_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_12_12

theorem valid_12_12 :
    SparseRowValid (![0, 0, 12, 12] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 12, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 12 + 12 = 24
      decide
    have hzsq : (∑ i, (((![0, 0, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 288 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 12^2 + 12^2 = 288
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_12_12
#print axioms Paper7MomentBlock00.valid_12_12

def qvalues_12_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_12_12

theorem row_12_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩⟩) = 20 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 12, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 12, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_12) :=
      sparseRow_sound (![0, 0, 12, 12] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_12_12) valid_12_12
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_12_12 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentBlock00.row_12_12

theorem row_12_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 12, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 13 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 13^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_13

theorem row_12_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 12, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 14 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 14^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_14

theorem row_12_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 12, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 15^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_15

theorem row_12_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 12, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 16^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_16

theorem row_12_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 12, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 17^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_17

theorem row_12_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 12, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 18^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_18

theorem row_12_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 12, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 19^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_19

theorem row_12_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 12, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 544 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 20^2 = 544
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_20

theorem row_12_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 12, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 21^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_21

theorem row_12_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 12, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 22 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 628 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 22^2 = 628
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_22

theorem row_12_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 12, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 673 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 23^2 = 673
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_23

theorem row_12_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 12, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 720 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 24^2 = 720
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_24

theorem row_12_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 12, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 12, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 12 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 12, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 769 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 12^2 + 25^2 = 769
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_12_25

def values_12 : Fin 26 → ℕ := ![0, 0, 0, 0, 1, 2, 7, 2, 5, 17, 8, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_12

theorem column_12 :
    (∑ d : Fin 26, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, d⟩)) = 62 := by
  calc
    (∑ d : Fin 26, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨12, by decide⟩, d⟩)) =
        ∑ d : Fin 26, values_12 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_12_00
      · exact row_12_01
      · exact row_12_02
      · exact row_12_03
      · exact row_12_04
      · exact row_12_05
      · exact row_12_06
      · exact row_12_07
      · exact row_12_08
      · exact row_12_09
      · exact row_12_10
      · exact row_12_11
      · exact row_12_12
      · exact row_12_13
      · exact row_12_14
      · exact row_12_15
      · exact row_12_16
      · exact row_12_17
      · exact row_12_18
      · exact row_12_19
      · exact row_12_20
      · exact row_12_21
      · exact row_12_22
      · exact row_12_23
      · exact row_12_24
      · exact row_12_25
    _ = 62 := by decide
#print axioms Paper7MomentBlock00.column_12

end Paper7MomentBlock00
