import Research.Backfill.Paper7.MomentB4Block00C00
import Research.Backfill.Paper7.B4RawOrbitWeights

/-! Source-only repeated-coordinate prototype for the saved row (0,0,0,7).
All nineteen Q decisions, every DP cell and the original row value come from
the successful block-00 producer. Only the actual orbit/gap assembly is new. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentNumericPrototype
open Paper7MomentCertificate Paper7MomentReduction

theorem repeated_cells :
    QTableValid (![0, 0, 0, 7] : Fin 4 → ℕ) Paper7MomentBlock00.layers_00_07 :=
  Paper7MomentBlock00.cells_00_07
#print axioms Paper7MomentNumericPrototype.repeated_cells

theorem repeated_accept_iff (Q : Fin 19) :
    B4CatalogRowAccept (![0, 0, 0, 7] : Fin 4 → ℕ) Q.val ↔
      Q ∈ ({7} : Finset (Fin 19)) :=
  Paper7MomentBlock00.valid_00_07.1 Q
#print axioms Paper7MomentNumericPrototype.repeated_accept_iff

theorem repeated_row_contribution :
    b4RowContribution (![0, 0, 0, 7] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 0, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_07
#print axioms Paper7MomentNumericPrototype.repeated_row_contribution

theorem repeated_orbit_weight : b4RawOrbitWeight (![0, 0, 0, 7] : Fin 4 → ℕ) = 4 := by
  rw [b4RawOrbitWeight_vector_eq_pattern 0 0 0 7 (by decide) (by decide) (by decide)]
  rfl
#print axioms Paper7MomentNumericPrototype.repeated_orbit_weight

theorem repeated_gap_contribution : b4RawGapContribution ![0, 0, 0, 7] = 4 := by
  calc
    b4RawGapContribution ![0, 0, 0, 7] =
        b4GapPatternWeight 0 0 7 * b4RowContribution ![0, 0, 0, 7] :=
      b4RawGapContribution_eq_pattern 0 0 0 7
    _ = 4 := by rw [repeated_row_contribution]; decide
#print axioms Paper7MomentNumericPrototype.repeated_gap_contribution

theorem repeated_complete :
    (∀ Q : Fin 19, B4CatalogRowAccept (![0, 0, 0, 7] : Fin 4 → ℕ) Q.val ↔
      Q ∈ ({7} : Finset (Fin 19))) ∧
    QTableValid (![0, 0, 0, 7] : Fin 4 → ℕ) Paper7MomentBlock00.layers_00_07 ∧
    b4RowContribution (![0, 0, 0, 7] : Fin 4 → ℕ) = 1 ∧
    b4RawOrbitWeight (![0, 0, 0, 7] : Fin 4 → ℕ) = 4 ∧
    b4RawGapContribution ![0, 0, 0, 7] = 4 :=
  ⟨repeated_accept_iff, repeated_cells, repeated_row_contribution,
    repeated_orbit_weight, repeated_gap_contribution⟩
#print axioms Paper7MomentNumericPrototype.repeated_complete

end Paper7MomentNumericPrototype
