import Research.Backfill.Paper7.GapWeightedBlocks

/-! Source-only certificate assembly over the complete original gap ranges.
Each generic hypothesis is a local proof obligation for a supplied finite
vector. The future generated numerical theorem must discharge every such
obligation and has no certificate, coverage or numerical-total premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentReduction
open Paper7MomentCertificate
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b4GapContribution_from_row (a b c d n : ℕ)
    (hrow : b4RowContribution ![a, a + b, a + b + c, a + b + c + d] = n) :
    b4RawGapContribution ![a, b, c, d] = b4GapPatternWeight b c d * n := by
  rw [b4RawGapContribution_eq_pattern, hrow]
#print axioms Paper7MomentReduction.b4GapContribution_from_row

theorem b4GapDBlock_of_rows (a b c : ℕ)
    (V : Fin (37 - 4 * a - 3 * b - 2 * c + 1) → ℕ)
    (hrow : ∀ d : Fin (37 - 4 * a - 3 * b - 2 * c + 1),
      b4RawGapContribution ![a, b, c, d.val] = V d) :
    b4GapPatternDBlock a b c = ∑ d, V d := by
  rw [← b4GapDBlock_eq_pattern]
  unfold b4GapDBlock
  calc
    (∑ d ∈ Finset.range (37 - 4 * a - 3 * b - 2 * c + 1),
        b4RawGapContribution ![a, b, c, d]) =
        ∑ d : Fin (37 - 4 * a - 3 * b - 2 * c + 1),
          b4RawGapContribution ![a, b, c, d.val] :=
      (Fin.sum_univ_eq_sum_range
        (fun d => b4RawGapContribution ![a, b, c, d])
        (37 - 4 * a - 3 * b - 2 * c + 1)).symm
    _ = ∑ d, V d := Finset.sum_congr rfl (fun d _ => hrow d)
#print axioms Paper7MomentReduction.b4GapDBlock_of_rows

def b4GapCBlock (a b : ℕ) : ℕ :=
  ∑ c ∈ Finset.range ((37 - 4 * a - 3 * b) / 2 + 1), b4GapPatternDBlock a b c
#print axioms Paper7MomentReduction.b4GapCBlock

theorem b4GapCBlock_of_dblocks (a b : ℕ)
    (V : Fin ((37 - 4 * a - 3 * b) / 2 + 1) → ℕ)
    (hblock : ∀ c : Fin ((37 - 4 * a - 3 * b) / 2 + 1),
      b4GapPatternDBlock a b c.val = V c) :
    b4GapCBlock a b = ∑ c, V c := by
  unfold b4GapCBlock
  calc
    (∑ c ∈ Finset.range ((37 - 4 * a - 3 * b) / 2 + 1),
        b4GapPatternDBlock a b c) =
        ∑ c : Fin ((37 - 4 * a - 3 * b) / 2 + 1),
          b4GapPatternDBlock a b c.val :=
      (Fin.sum_univ_eq_sum_range (fun c => b4GapPatternDBlock a b c)
        ((37 - 4 * a - 3 * b) / 2 + 1)).symm
    _ = ∑ c, V c := Finset.sum_congr rfl (fun c _ => hblock c)
#print axioms Paper7MomentReduction.b4GapCBlock_of_dblocks

def b4GapABlock (a : ℕ) : ℕ :=
  ∑ b ∈ Finset.range ((37 - 4 * a) / 3 + 1), b4GapCBlock a b
#print axioms Paper7MomentReduction.b4GapABlock

theorem b4GapABlock_of_cblocks (a : ℕ)
    (V : Fin ((37 - 4 * a) / 3 + 1) → ℕ)
    (hblock : ∀ b : Fin ((37 - 4 * a) / 3 + 1), b4GapCBlock a b.val = V b) :
    b4GapABlock a = ∑ b, V b := by
  unfold b4GapABlock
  calc
    (∑ b ∈ Finset.range ((37 - 4 * a) / 3 + 1), b4GapCBlock a b) =
        ∑ b : Fin ((37 - 4 * a) / 3 + 1), b4GapCBlock a b.val :=
      (Fin.sum_univ_eq_sum_range (fun b => b4GapCBlock a b)
        ((37 - 4 * a) / 3 + 1)).symm
    _ = ∑ b, V b := Finset.sum_congr rfl (fun b _ => hblock b)
#print axioms Paper7MomentReduction.b4GapABlock_of_cblocks

theorem candB1_b4_ncard_eq_gap_ablocks :
    (CandB1 4 41).ncard = ∑ a : Fin 10, b4GapABlock a.val := by
  calc
    (CandB1 4 41).ncard =
        ∑ a ∈ Finset.range (37 / 4 + 1), b4GapABlock a :=
      candB1_b4_ncard_eq_gap_pattern_dblocks
    _ = ∑ a : Fin 10, b4GapABlock a.val :=
      (Fin.sum_univ_eq_sum_range b4GapABlock 10).symm
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_ablocks

theorem candB1_b4_ncard_of_ablocks (V : Fin 10 → ℕ)
    (hblock : ∀ a : Fin 10, b4GapABlock a.val = V a) :
    (CandB1 4 41).ncard = ∑ a, V a := by
  rw [candB1_b4_ncard_eq_gap_ablocks]
  exact Finset.sum_congr rfl (fun a _ => hblock a)
#print axioms Paper7MomentReduction.candB1_b4_ncard_of_ablocks

end Paper7MomentReduction
