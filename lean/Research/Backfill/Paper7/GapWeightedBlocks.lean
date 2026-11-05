import Research.Backfill.Paper7.GapNestedSum
import Research.Backfill.Paper7.B4RawOrbitWeights

/-! Source-only assembly. Only the proved equality-pattern weight is evaluated
symbolically here; every row contribution and every numerical block sum remains
a separate kernel obligation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7MomentCertificate
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b4GapPatternDBlock (a b c : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (37 - 4 * a - 3 * b - 2 * c + 1),
    b4GapPatternWeight b c d *
      b4RowContribution ![a, a + b, a + b + c, a + b + c + d]
#print axioms Paper7MomentReduction.b4GapPatternDBlock

theorem b4GapDBlock_eq_pattern (a b c : ℕ) :
    b4GapDBlock a b c = b4GapPatternDBlock a b c := by
  unfold b4GapDBlock b4GapPatternDBlock
  exact Finset.sum_congr rfl (fun d _ => b4RawGapContribution_eq_pattern a b c d)
#print axioms Paper7MomentReduction.b4GapDBlock_eq_pattern

theorem candB1_b4_ncard_eq_gap_pattern_dblocks :
    (CandB1 4 41).ncard =
      ∑ a ∈ Finset.range (37 / 4 + 1),
        ∑ b ∈ Finset.range ((37 - 4 * a) / 3 + 1),
          ∑ c ∈ Finset.range ((37 - 4 * a - 3 * b) / 2 + 1),
            b4GapPatternDBlock a b c := by
  rw [candB1_b4_ncard_eq_gap_dblocks]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  exact Finset.sum_congr rfl (fun c _ => b4GapDBlock_eq_pattern a b c)
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_pattern_dblocks

end Paper7MomentReduction
