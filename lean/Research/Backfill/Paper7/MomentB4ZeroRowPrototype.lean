import Research.Backfill.Paper7.MomentB4Block00C00
import Research.Backfill.Paper7.B4RawOrbitWeights

/-! Source-only zero-row prototype. The original row value is reused from the
actual successful block-00 producer. The candidate data has no DP table for
this rejected row; the elementary table below is a new symbolic certificate,
not an inferred candidate table. No whole-domain count is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentNumericPrototype
open Paper7MomentCertificate Paper7MomentReduction
open scoped BigOperators

def zeroLayers : Fin 5 → Fin 19 → ℕ := fun _ t => if t.val = 0 then 1 else 0
#print axioms Paper7MomentNumericPrototype.zeroLayers

theorem zero_cells : QTableValid (![0, 0, 0, 0] : Fin 4 → ℕ) zeroLayers := by
  unfold QTableValid
  constructor
  · intro t
    rfl
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentNumericPrototype.zero_cells

theorem zero_accept_iff (Q : Fin 19) :
    B4CatalogRowAccept (![0, 0, 0, 0] : Fin 4 → ℕ) Q.val ↔
      Q ∈ (∅ : Finset (Fin 19)) := by
  constructor
  · intro h
    have hz : (∑ i, (![0, 0, 0, 0] : Fin 4 → ℕ) i) = 0 := by decide
    have hq : Q.val ≤ 0 := by simpa only [hz] using h.1
    have hp : 0 < Q.val := by simpa only [hz, Nat.zero_add] using h.2.1
    omega
  · intro h
    exact False.elim (Finset.notMem_empty Q h)
#print axioms Paper7MomentNumericPrototype.zero_accept_iff

theorem zero_row_contribution :
    b4RowContribution (![0, 0, 0, 0] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩, ⟨0, by decide⟩⟩ = (![0, 0, 0, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_00_00
#print axioms Paper7MomentNumericPrototype.zero_row_contribution

theorem zero_orbit_weight : b4RawOrbitWeight (![0, 0, 0, 0] : Fin 4 → ℕ) = 1 := by
  rw [b4RawOrbitWeight_vector_eq_pattern 0 0 0 0 (by decide) (by decide) (by decide)]
  rfl
#print axioms Paper7MomentNumericPrototype.zero_orbit_weight

theorem zero_gap_contribution : b4RawGapContribution ![0, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 0, 0] =
        b4GapPatternWeight 0 0 0 * b4RowContribution ![0, 0, 0, 0] :=
      b4RawGapContribution_eq_pattern 0 0 0 0
    _ = 0 := by rw [zero_row_contribution, Nat.mul_zero]
#print axioms Paper7MomentNumericPrototype.zero_gap_contribution

theorem zero_complete :
    (∀ Q : Fin 19, B4CatalogRowAccept (![0, 0, 0, 0] : Fin 4 → ℕ) Q.val ↔
      Q ∈ (∅ : Finset (Fin 19))) ∧
    QTableValid (![0, 0, 0, 0] : Fin 4 → ℕ) zeroLayers ∧
    b4RowContribution (![0, 0, 0, 0] : Fin 4 → ℕ) = 0 ∧
    b4RawOrbitWeight (![0, 0, 0, 0] : Fin 4 → ℕ) = 1 ∧
    b4RawGapContribution ![0, 0, 0, 0] = 0 :=
  ⟨zero_accept_iff, zero_cells, zero_row_contribution, zero_orbit_weight,
    zero_gap_contribution⟩
#print axioms Paper7MomentNumericPrototype.zero_complete

end Paper7MomentNumericPrototype
