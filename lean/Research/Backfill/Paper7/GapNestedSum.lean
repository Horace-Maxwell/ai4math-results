import Research.Backfill.Paper7.MomentB4GapSum

/-! Source-only complete finite partition. Disjointness is proved by reading
the fixed prefix coordinates; the last coordinate map is injective.
No table, cardinality 5615, or numerical sum is a coverage assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SortedGaps
open scoped BigOperators Classical

def gapTailFinset (B a b c : ℕ) : Finset (Fin 4 → ℕ) :=
  (Finset.range (B - 4 * a - 3 * b - 2 * c + 1)).image fun d => ![a, b, c, d]
#print axioms Paper7SortedGaps.gapTailFinset

def gapThirdFinset (B a b : ℕ) : Finset (Fin 4 → ℕ) :=
  (Finset.range ((B - 4 * a - 3 * b) / 2 + 1)).biUnion (gapTailFinset B a b)
#print axioms Paper7SortedGaps.gapThirdFinset

def gapSecondFinset (B a : ℕ) : Finset (Fin 4 → ℕ) :=
  (Finset.range ((B - 4 * a) / 3 + 1)).biUnion (gapThirdFinset B a)
#print axioms Paper7SortedGaps.gapSecondFinset

theorem mem_gapTail_prefix (B a b c : ℕ) (g : Fin 4 → ℕ)
    (hg : g ∈ gapTailFinset B a b c) : g 0 = a ∧ g 1 = b ∧ g 2 = c := by
  unfold gapTailFinset at hg
  obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨rfl, rfl, rfl⟩
#print axioms Paper7SortedGaps.mem_gapTail_prefix

theorem mem_gapThird_prefix (B a b : ℕ) (g : Fin 4 → ℕ)
    (hg : g ∈ gapThirdFinset B a b) : g 0 = a ∧ g 1 = b := by
  unfold gapThirdFinset at hg
  obtain ⟨c, _hc, hgc⟩ := Finset.mem_biUnion.mp hg
  exact ⟨(mem_gapTail_prefix B a b c g hgc).1,
    (mem_gapTail_prefix B a b c g hgc).2.1⟩
#print axioms Paper7SortedGaps.mem_gapThird_prefix

theorem mem_gapSecond_prefix (B a : ℕ) (g : Fin 4 → ℕ)
    (hg : g ∈ gapSecondFinset B a) : g 0 = a := by
  unfold gapSecondFinset at hg
  obtain ⟨b, _hb, hgb⟩ := Finset.mem_biUnion.mp hg
  exact (mem_gapThird_prefix B a b g hgb).1
#print axioms Paper7SortedGaps.mem_gapSecond_prefix

theorem gapTail_pairwiseDisjoint (B a b : ℕ) :
    Set.PairwiseDisjoint
      (↑(Finset.range ((B - 4 * a - 3 * b) / 2 + 1))) (gapTailFinset B a b) := by
  intro c _hc e _he hne
  apply Finset.disjoint_left.mpr
  intro g hgc hge
  exact hne ((mem_gapTail_prefix B a b c g hgc).2.2.symm.trans
    (mem_gapTail_prefix B a b e g hge).2.2)
#print axioms Paper7SortedGaps.gapTail_pairwiseDisjoint

theorem gapThird_pairwiseDisjoint (B a : ℕ) :
    Set.PairwiseDisjoint
      (↑(Finset.range ((B - 4 * a) / 3 + 1))) (gapThirdFinset B a) := by
  intro b _hb e _he hne
  apply Finset.disjoint_left.mpr
  intro g hgb hge
  exact hne ((mem_gapThird_prefix B a b g hgb).2.symm.trans
    (mem_gapThird_prefix B a e g hge).2)
#print axioms Paper7SortedGaps.gapThird_pairwiseDisjoint

theorem gapSecond_pairwiseDisjoint (B : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (B / 4 + 1))) (gapSecondFinset B) := by
  intro a _ha e _he hne
  apply Finset.disjoint_left.mpr
  intro g hga hge
  exact hne ((mem_gapSecond_prefix B a g hga).symm.trans
    (mem_gapSecond_prefix B e g hge))
#print axioms Paper7SortedGaps.gapSecond_pairwiseDisjoint

theorem sum_gapTail (B a b c : ℕ) (f : (Fin 4 → ℕ) → ℕ) :
    (∑ g ∈ gapTailFinset B a b c, f g) =
      ∑ d ∈ Finset.range (B - 4 * a - 3 * b - 2 * c + 1), f ![a, b, c, d] := by
  unfold gapTailFinset
  apply Finset.sum_image
  intro d _hd e _he h
  exact congrFun h (3 : Fin 4)
#print axioms Paper7SortedGaps.sum_gapTail

theorem sum_gapThird (B a b : ℕ) (f : (Fin 4 → ℕ) → ℕ) :
    (∑ g ∈ gapThirdFinset B a b, f g) =
      ∑ c ∈ Finset.range ((B - 4 * a - 3 * b) / 2 + 1),
        ∑ d ∈ Finset.range (B - 4 * a - 3 * b - 2 * c + 1), f ![a, b, c, d] := by
  calc
    (∑ g ∈ gapThirdFinset B a b, f g) =
        ∑ c ∈ Finset.range ((B - 4 * a - 3 * b) / 2 + 1),
          ∑ g ∈ gapTailFinset B a b c, f g :=
      Finset.sum_biUnion (gapTail_pairwiseDisjoint B a b)
    _ = _ := Finset.sum_congr rfl (fun c _ => sum_gapTail B a b c f)
#print axioms Paper7SortedGaps.sum_gapThird

theorem sum_gapSecond (B a : ℕ) (f : (Fin 4 → ℕ) → ℕ) :
    (∑ g ∈ gapSecondFinset B a, f g) =
      ∑ b ∈ Finset.range ((B - 4 * a) / 3 + 1),
        ∑ c ∈ Finset.range ((B - 4 * a - 3 * b) / 2 + 1),
          ∑ d ∈ Finset.range (B - 4 * a - 3 * b - 2 * c + 1), f ![a, b, c, d] := by
  calc
    (∑ g ∈ gapSecondFinset B a, f g) =
        ∑ b ∈ Finset.range ((B - 4 * a) / 3 + 1),
          ∑ g ∈ gapThirdFinset B a b, f g :=
      Finset.sum_biUnion (gapThird_pairwiseDisjoint B a)
    _ = _ := Finset.sum_congr rfl (fun b _ => sum_gapThird B a b f)
#print axioms Paper7SortedGaps.sum_gapSecond

/-- Full-domain equality, including every zero and repeated-coordinate row. -/
theorem sum_gapFinset_eq_nested (B : ℕ) (f : (Fin 4 → ℕ) → ℕ) :
    (∑ g ∈ gapFinset B, f g) =
      ∑ a ∈ Finset.range (B / 4 + 1),
        ∑ b ∈ Finset.range ((B - 4 * a) / 3 + 1),
          ∑ c ∈ Finset.range ((B - 4 * a - 3 * b) / 2 + 1),
            ∑ d ∈ Finset.range (B - 4 * a - 3 * b - 2 * c + 1), f ![a, b, c, d] := by
  calc
    (∑ g ∈ gapFinset B, f g) =
        ∑ a ∈ Finset.range (B / 4 + 1), ∑ g ∈ gapSecondFinset B a, f g :=
      Finset.sum_biUnion (gapSecond_pairwiseDisjoint B)
    _ = _ := Finset.sum_congr rfl (fun a _ => sum_gapSecond B a f)
#print axioms Paper7SortedGaps.sum_gapFinset_eq_nested

end Paper7SortedGaps

namespace Paper7MomentReduction
open Paper7SortedGaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

/-- A full d interval. Only legal a/b/c prefixes are used in the total below. -/
def b4GapDBlock (a b c : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (37 - 4 * a - 3 * b - 2 * c + 1),
    b4RawGapContribution ![a, b, c, d]
#print axioms Paper7MomentReduction.b4GapDBlock

theorem candB1_b4_ncard_eq_gap_nested_sum :
    (CandB1 4 41).ncard =
      ∑ a ∈ Finset.range (37 / 4 + 1),
        ∑ b ∈ Finset.range ((37 - 4 * a) / 3 + 1),
          ∑ c ∈ Finset.range ((37 - 4 * a - 3 * b) / 2 + 1),
            ∑ d ∈ Finset.range (37 - 4 * a - 3 * b - 2 * c + 1),
              b4RawGapContribution ![a, b, c, d] :=
  candB1_b4_ncard_eq_gap_finset_sum.trans
    (sum_gapFinset_eq_nested 37 b4RawGapContribution)
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_nested_sum

theorem candB1_b4_ncard_eq_gap_dblocks :
    (CandB1 4 41).ncard =
      ∑ a ∈ Finset.range (37 / 4 + 1),
        ∑ b ∈ Finset.range ((37 - 4 * a) / 3 + 1),
          ∑ c ∈ Finset.range ((37 - 4 * a - 3 * b) / 2 + 1), b4GapDBlock a b c :=
  candB1_b4_ncard_eq_gap_nested_sum
#print axioms Paper7MomentReduction.candB1_b4_ncard_eq_gap_dblocks

end Paper7MomentReduction
