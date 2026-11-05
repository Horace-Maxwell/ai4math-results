import Research.Backfill.Paper7.MomentB4Block00C03
import Research.Backfill.Paper7.B4RawOrbitWeights

/-! Source-only multi-Q prototype for the saved row (0,0,3,15). The three
accepted Q values use one complete actual DP table, already proved in the
successful block-00 producer. Each Q is counted once. Its gap is (0,0,3,12),
which is different from its sorted row; the actual orbit weight is twelve. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentNumericPrototype
open Paper7MomentCertificate Paper7MomentReduction

theorem multi_cells :
    QTableValid (![0, 0, 3, 15] : Fin 4 → ℕ) Paper7MomentBlock00.layers_03_15 :=
  Paper7MomentBlock00.cells_03_15
#print axioms Paper7MomentNumericPrototype.multi_cells

theorem multi_accept_iff (Q : Fin 19) :
    B4CatalogRowAccept (![0, 0, 3, 15] : Fin 4 → ℕ) Q.val ↔
      Q ∈ ({6, 12, 18} : Finset (Fin 19)) :=
  Paper7MomentBlock00.valid_03_15.1 Q
#print axioms Paper7MomentNumericPrototype.multi_accept_iff

theorem multi_last_layer :
    Paper7MomentBlock00.layers_03_15 (Fin.last 4) 6 = 4 ∧
    Paper7MomentBlock00.layers_03_15 (Fin.last 4) 12 = 4 ∧
    Paper7MomentBlock00.layers_03_15 (Fin.last 4) 18 = 1 := by decide
#print axioms Paper7MomentNumericPrototype.multi_last_layer

theorem multi_row_contribution :
    b4RowContribution (![0, 0, 3, 15] : Fin 4 → ℕ) = 9 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨3, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 3, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_03_15
#print axioms Paper7MomentNumericPrototype.multi_row_contribution

theorem multi_orbit_weight : b4RawOrbitWeight (![0, 0, 3, 15] : Fin 4 → ℕ) = 12 := by
  rw [b4RawOrbitWeight_vector_eq_pattern 0 0 3 15 (by decide) (by decide) (by decide)]
  rfl
#print axioms Paper7MomentNumericPrototype.multi_orbit_weight

theorem multi_gap_contribution : b4RawGapContribution ![0, 0, 3, 12] = 108 := by
  calc
    b4RawGapContribution ![0, 0, 3, 12] =
        b4GapPatternWeight 0 3 12 * b4RowContribution ![0, 0, 3, 15] :=
      b4RawGapContribution_eq_pattern 0 0 3 12
    _ = 108 := by rw [multi_row_contribution]; decide
#print axioms Paper7MomentNumericPrototype.multi_gap_contribution

theorem multi_complete :
    (∀ Q : Fin 19, B4CatalogRowAccept (![0, 0, 3, 15] : Fin 4 → ℕ) Q.val ↔
      Q ∈ ({6, 12, 18} : Finset (Fin 19))) ∧
    QTableValid (![0, 0, 3, 15] : Fin 4 → ℕ) Paper7MomentBlock00.layers_03_15 ∧
    b4RowContribution (![0, 0, 3, 15] : Fin 4 → ℕ) = 9 ∧
    b4RawOrbitWeight (![0, 0, 3, 15] : Fin 4 → ℕ) = 12 ∧
    b4RawGapContribution ![0, 0, 3, 12] = 108 :=
  ⟨multi_accept_iff, multi_cells, multi_row_contribution, multi_orbit_weight,
    multi_gap_contribution⟩
#print axioms Paper7MomentNumericPrototype.multi_complete

end Paper7MomentNumericPrototype
