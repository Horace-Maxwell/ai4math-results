import Research.Backfill.Paper7.SortedGapCoordinates
import Research.Backfill.Paper7.MomentB4SortedSum

/-! Source-only candidate. Transport the original complete B1 cardinality to
the explicit finite gap domain, preserving the actual distinct-orbit weights.
No total 410544, representative count 5615, or candidate-table completeness
is a hypothesis or conclusion of this file. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7Budget Paper7SortedRows Paper7SortedGaps Paper7MomentCertificate
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b4GapWeight (g : GapTuple 37) : ℕ := orbitWeight (gapToSorted g).val
#print axioms Paper7MomentReduction.b4GapWeight

def b4GapContribution (g : GapTuple 37) : ℕ :=
  b4GapWeight g * b4RowContribution (prefixRow g.val)
#print axioms Paper7MomentReduction.b4GapContribution

theorem b4GapWeight_pos (g : GapTuple 37) : 0 < b4GapWeight g :=
  orbitWeight_pos (gapToSorted g).val
#print axioms Paper7MomentReduction.b4GapWeight_pos

theorem b4GapWeight_mul_multiplicities (g : GapTuple 37) :
    b4GapWeight g *
      (∏ v ∈ Finset.univ.image (prefixRow g.val),
        (Fintype.card {i : Fin 4 // prefixRow g.val i = v}).factorial) = 24 := by
  exact b4_orbitWeight_mul_multiplicities (gapToSorted g).val
#print axioms Paper7MomentReduction.b4GapWeight_mul_multiplicities

/-- Whole original labelled count; all gap coordinates in the budget occur. -/
theorem candB1_b4_ncard_eq_gap_weighted_rows :
    (CandB1 4 41).ncard = ∑ g : GapTuple 37, b4GapContribution g := by
  exact candB1_b4_ncard_eq_sorted_weighted_rows.trans
    (sum_sorted_eq_gap 37 (fun r : SortedTuple 4 37 =>
      orbitWeight r.val * b4RowContribution r.val.val))
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_weighted_rows

/-- Raw-row form of the same genuine orbit, with duplicate permutations removed. -/
def b4RawOrbitWeight (z : Fin 4 → ℕ) : ℕ :=
  (Finset.univ.image (fun e : Equiv.Perm (Fin 4) => z ∘ e)).card
#print axioms Paper7MomentReduction.b4RawOrbitWeight

theorem b4_orbitWeight_eq_raw {B : ℕ} (x : BoundedTuple 4 B) :
    orbitWeight x = b4RawOrbitWeight x.val := by
  have himage : (orbitFinset x).image (fun y : BoundedTuple 4 B => y.val) =
      Finset.univ.image (fun e : Equiv.Perm (Fin 4) => x.val ∘ e) := by
    simp only [orbitFinset, Finset.image_image, permute, Function.comp_def]
  unfold orbitWeight b4RawOrbitWeight
  rw [← himage]
  exact (Finset.card_image_of_injective (orbitFinset x) Subtype.val_injective).symm
#print axioms Paper7MomentReduction.b4_orbitWeight_eq_raw

theorem b4GapWeight_eq_raw (g : GapTuple 37) :
    b4GapWeight g = b4RawOrbitWeight (prefixRow g.val) :=
  b4_orbitWeight_eq_raw (gapToSorted g).val
#print axioms Paper7MomentReduction.b4GapWeight_eq_raw

def b4RawGapContribution (g : Fin 4 → ℕ) : ℕ :=
  b4RawOrbitWeight (prefixRow g) * b4RowContribution (prefixRow g)
#print axioms Paper7MomentReduction.b4RawGapContribution

theorem b4GapContribution_eq_raw (g : GapTuple 37) :
    b4GapContribution g = b4RawGapContribution g.val := by
  unfold b4GapContribution b4RawGapContribution
  rw [b4GapWeight_eq_raw]
#print axioms Paper7MomentReduction.b4GapContribution_eq_raw

/-- The explicit finite sum is the entire original domain, not a supplied list. -/
theorem candB1_b4_ncard_eq_gap_finset_sum :
    (CandB1 4 41).ncard = ∑ g ∈ gapFinset 37, b4RawGapContribution g := by
  calc
    (CandB1 4 41).ncard = ∑ g : GapTuple 37, b4GapContribution g :=
      candB1_b4_ncard_eq_gap_weighted_rows
    _ = ∑ g : GapTuple 37, b4RawGapContribution g.val :=
      Finset.sum_congr rfl (fun g _ => b4GapContribution_eq_raw g)
    _ = ∑ g ∈ gapFinset 37, b4RawGapContribution g := Finset.sum_coe_sort _ _
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_finset_sum

end Paper7MomentReduction
