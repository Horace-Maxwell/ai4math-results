import Research.Backfill.Paper7.SortedTupleWeights
import Research.Backfill.Paper7.MomentB4RowSymmetry

/-! Source-only candidate. This preserves the complete labelled B1 domain.
It does not assert the total 410544 or any of the other seven frozen numbers. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7Budget Paper7SortedRows Paper7MomentCertificate
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

/-- Each S4 orbit is weighted by its actual number of distinct ordered rows. -/
theorem b4_orbitWeight_mul_stabilizer (x : BoundedTuple 4 37) :
    orbitWeight x * Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin 4)) x) = 24 := by
  exact orbitWeight_mul_stabilizer x
#print axioms Paper7MomentReduction.b4_orbitWeight_mul_stabilizer

theorem b4_orbitWeight_mul_multiplicities (x : BoundedTuple 4 37) :
    orbitWeight x *
      (∏ v ∈ Finset.univ.image x.val, (Fintype.card {i : Fin 4 // x.val i = v}).factorial) =
      24 := by
  exact orbitWeight_mul_multiplicities x
#print axioms Paper7MomentReduction.b4_orbitWeight_mul_multiplicities

/-- Complete original B1 cardinality, with no numerical or coverage premise. -/
theorem candB1_b4_ncard_eq_sorted_weighted_rows :
    (CandB1 4 41).ncard =
      ∑ r : SortedTuple 4 37, orbitWeight r.val * b4RowContribution r.val.val := by
  rw [candB1_b4_ncard_eq_row_contributions]
  apply sum_sorted_weighted (fun x : BoundedTuple 4 37 => b4RowContribution x.val)
  intro e x
  change b4RowContribution (x.val ∘ e) = b4RowContribution x.val
  exact b4RowContribution_comp_perm x.val e
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_sorted_weighted_rows

end Paper7MomentReduction
