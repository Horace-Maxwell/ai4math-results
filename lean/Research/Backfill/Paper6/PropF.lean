import Research.Backfill.Paper6.Lem51

/-!
# Paper 6 V3: the complete directional criterion and all four counting bounds

The pair decomposition is reused with its full quantifier over prescribed
linear coordinate equivalences. Odd pair counts give a counting inequality
for directions with count one or three. Conversely, actual lower-dimensional
RM words are combined as g+x14*h, and the full Lem22 supplies membership and
the exact support-difference weight formula.

Frozen FROZEN.json SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Candidate source only; root controls compilation and acceptance.
-/

set_option autoImplicit false

namespace Paper6DirectionCriterion

open BackfillPaper6.V3

noncomputable def nonzeroDirections : Finset (Pt 14) :=
  Finset.univ.erase 0

noncomputable def goodDirections (f : BFun 14) : Finset (Pt 14) := by
  classical
  exact nonzeroDirections.filter fun a => pairCount f a = 1 ∨ pairCount f a = 3

theorem card_nonzeroDirections : nonzeroDirections.card = 16383 := by
  classical
  rw [nonzeroDirections, Finset.card_erase_of_mem (Finset.mem_univ (0 : Pt 14)),
    Finset.card_univ]
  norm_num [Pt]

theorem mem_goodDirections (f : BFun 14) (a : Pt 14) :
    a ∈ goodDirections f ↔ a ≠ 0 ∧ (pairCount f a = 1 ∨ pairCount f a = 3) := by
  classical
  simp [goodDirections, nonzeroDirections]

/-- Good directions contribute at least one, all other odd counts contribute at least five. -/
theorem good_direction_budget (f : BFun 14) (hf : f ∈ RM 7 14)
    (hmod : hammingNorm f % 4 = 2) :
    81915 ≤ (hammingNorm f).choose 2 + 4 * (goodDirections f).card := by
  classical
  have hlem := Paper6PairDecomposition.check_Lem51 f hf hmod
  have hpoint (a : Pt 14) (ha : a ∈ nonzeroDirections) :
      5 ≤ pairCount f a + 4 * (if pairCount f a = 1 ∨ pairCount f a = 3 then 1 else 0) := by
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    obtain ⟨k, hk⟩ := hlem.2.1 a ha0
    by_cases hg : pairCount f a = 1 ∨ pairCount f a = 3
    · rw [ite_eq_left hg]
      omega
    · rw [ite_eq_right hg]
      have hn1 : pairCount f a ≠ 1 := fun h => hg (Or.inl h)
      have hn3 : pairCount f a ≠ 3 := fun h => hg (Or.inr h)
      omega
  have hbudget : 5 * nonzeroDirections.card ≤
      (∑ a ∈ nonzeroDirections, pairCount f a) + 4 * (goodDirections f).card := by
    calc
      5 * nonzeroDirections.card = ∑ _a ∈ nonzeroDirections, (5 : ℕ) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ nonzeroDirections,
          (pairCount f a + 4 * (if pairCount f a = 1 ∨ pairCount f a = 3 then 1 else 0)) :=
        Finset.sum_le_sum (fun a ha => hpoint a ha)
      _ = (∑ a ∈ nonzeroDirections, pairCount f a) + 4 * (goodDirections f).card := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, goodDirections,
          Nat.cast_id]
  have hsum : (∑ a ∈ nonzeroDirections, pairCount f a) = (hammingNorm f).choose 2 := hlem.1
  rw [card_nonzeroDirections, hsum] at hbudget
  exact hbudget

/-- The exact four parameter pairs from the frozen proposition. -/
def directionBounds : List (ℕ × ℕ) :=
  [(322, 7559), (326, 7235), (330, 6908), (334, 6576)]

/-- Each listed lower bound is forced by the pair-count budget; the strict threshold uses N-1. -/
theorem directionBounds_data :
    ∀ p ∈ directionBounds,
      p.1 % 4 = 2 ∧ 6 ≤ p.1 ∧ 0 < p.2 ∧
        p.1.choose 2 + 4 * (p.2 - 1) < 81915 := by
  norm_num [directionBounds, Nat.choose_two_right]

theorem exists_directionBound (w : ℕ) (hw : w ∈ U0) :
    ∃ N, (w, N) ∈ directionBounds := by
  simp only [U0, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨7559, by decide⟩
  · exact ⟨7235, by decide⟩
  · exact ⟨6908, by decide⟩
  · exact ⟨6576, by decide⟩

theorem good_card_lower_bound (f : BFun 14) (hf : f ∈ RM 7 14) (w N : ℕ)
    (hparam : (w, N) ∈ directionBounds) (hw : hammingNorm f = w) :
    N ≤ (goodDirections f).card := by
  have hdata := directionBounds_data (w, N) hparam
  have hmod : hammingNorm f % 4 = 2 := by rw [hw]; exact hdata.1
  have hbudget := good_direction_budget f hf hmod
  rw [hw] at hbudget
  have hthreshold : w.choose 2 + 4 * (N - 1) < 81915 := hdata.2.2.2
  omega

/-- Each good pair count gives the full DecompAt statement for every prescribed φ. -/
theorem decompAt_of_good (f : BFun 14) (hf : f ∈ RM 7 14) (w : ℕ)
    (hw : hammingNorm f = w) (hmod : hammingNorm f % 4 = 2)
    (a : Pt 14) (ha : a ∈ goodDirections f) : DecompAt f a w := by
  have hgood := (mem_goodDirections f a).mp ha
  intro φ hφ
  obtain ⟨g, hg, h, hh, hreconstruct, hpairs, hweight⟩ :=
    (Paper6PairDecomposition.check_Lem51 f hf hmod).2.2 a hgood.1 φ hφ
  refine ⟨g, hg, h, hh, hreconstruct, ?_⟩
  rcases hgood.2 with hn | hn
  · left
    constructor
    · rw [hn, hw] at hweight
      omega
    · rw [← hpairs, hn]
  · right
    constructor
    · rw [hn, hw] at hweight
      omega
    · rw [← hpairs, hn]

/-- The finite good-direction set is contained in the exact set counted by the frozen target. -/
theorem good_card_le_decomp_ncard (f : BFun 14) (hf : f ∈ RM 7 14) (w : ℕ)
    (hw : hammingNorm f = w) (hmod : hammingNorm f % 4 = 2) :
    (goodDirections f).card ≤ Set.ncard {a : Pt 14 | a ≠ 0 ∧ DecompAt f a w} := by
  classical
  have hsubset : (goodDirections f : Set (Pt 14)) ⊆ {a : Pt 14 | a ≠ 0 ∧ DecompAt f a w} := by
    intro a ha
    exact ⟨((mem_goodDirections f a).mp ha).1, decompAt_of_good f hf w hw hmod a ha⟩
  simpa only [Set.ncard_coe_finset] using Set.ncard_mono hsubset

/-- All four quantitative bounds, retaining the arbitrary input codeword f. -/
theorem direction_bound (f : BFun 14) (hf : f ∈ RM 7 14) (w N : ℕ)
    (hparam : (w, N) ∈ directionBounds) (hw : hammingNorm f = w) :
    N ≤ Set.ncard {a : Pt 14 | a ≠ 0 ∧ DecompAt f a w} := by
  have hmod : hammingNorm f % 4 = 2 := by
    rw [hw]
    exact (directionBounds_data (w, N) hparam).1
  exact (good_card_lower_bound f hf w N hparam hw).trans
    (good_card_le_decomp_ncard f hf w hw hmod)

/-- The positive quantitative bound supplies a nonzero direction and actual lower-dimensional words. -/
theorem forward_criterion (w : ℕ) (hw : w ∈ U0) (hweight : IsWeight 7 14 w) :
    ∃ h ∈ RM 6 13, ∃ g ∈ RM 7 13,
      (hammingNorm h = w - 2 ∧ (Function.support g \ Function.support h).ncard = 1) ∨
      (hammingNorm h = w - 6 ∧ (Function.support g \ Function.support h).ncard = 3) := by
  obtain ⟨f, hf, hfw⟩ := hweight
  obtain ⟨N, hparam⟩ := exists_directionBound w hw
  have hdata := directionBounds_data (w, N) hparam
  have hpositive : 0 < (goodDirections f).card :=
    lt_of_lt_of_le hdata.2.2.1 (good_card_lower_bound f hf w N hparam hfw)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpositive
  have hmod : hammingNorm f % 4 = 2 := by rw [hfw]; exact hdata.1
  have ha0 := ((mem_goodDirections f a).mp ha).1
  obtain ⟨φ, hφ⟩ := Paper6PairDecomposition.exists_direction_equiv a ha0
  obtain ⟨g, hg, h, hh, _hreconstruct, hcases⟩ :=
    decompAt_of_good f hf w hfw hmod a ha φ hφ
  exact ⟨h, hh, g, hg, hcases⟩

/-- The actual function used in the reverse implication. -/
def combine (g h : BFun 13) : BFun 14 :=
  fun y => g (Fin.init y) + y (Fin.last 13) * h (Fin.init y)

theorem half0_combine (g h : BFun 13) : half0 (combine g h) = g := by
  funext x
  change g (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 0)) +
    (Fin.snoc (α := fun _ => ZMod 2) x 0) (Fin.last 13) *
      h (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 0)) = g x
  rw [Fin.init_snoc, Fin.snoc_last, zero_mul, add_zero]

theorem half1_combine (g h : BFun 13) : half1 (combine g h) = g + h := by
  funext x
  change g (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 1)) +
    (Fin.snoc (α := fun _ => ZMod 2) x 1) (Fin.last 13) *
      h (Fin.init (Fin.snoc (α := fun _ => ZMod 2) x 1)) = g x + h x
  rw [Fin.init_snoc, Fin.snoc_last, one_mul]

theorem binary_cancel (g h : BFun 13) : g + (g + h) = h := by
  funext x
  change g x + (g x + h x) = h x
  exact CharTwo.add_cancel_left (g x) (h x)

theorem delta_combine (g h : BFun 13) : half0 (combine g h) + half1 (combine g h) = h := by
  rw [half0_combine, half1_combine, binary_cancel]

/-- The reverse construction has a genuine polynomial witness of degree at most seven. -/
theorem combine_mem_RM (g h : BFun 13) (hg : g ∈ RM 7 13) (hh : h ∈ RM 6 13) :
    combine g h ∈ RM 7 14 := by
  apply Paper6HalfDecomposition.rm_mem_of_slices 13 6
  · rw [half0_combine]
    exact hg
  · rw [delta_combine]
    exact hh

/-- Its actual Hamming weight is the exact support-difference formula used in the criterion. -/
theorem weight_combine (g h : BFun 13) :
    hammingNorm (combine g h) = hammingNorm h +
      2 * (Function.support g \ Function.support h).ncard := by
  rw [Paper6HalfDecomposition.weight_slices 13, half0_combine, half1_combine,
    Paper6HalfDecomposition.weight_add_with_intersection g (g + h), binary_cancel,
    Paper6HalfDecomposition.support_inter_eq_sdiff g (g + h), binary_cancel]

theorem reverse_criterion (w : ℕ) (hw : w ∈ U0)
    (hdata : ∃ h ∈ RM 6 13, ∃ g ∈ RM 7 13,
      (hammingNorm h = w - 2 ∧ (Function.support g \ Function.support h).ncard = 1) ∨
      (hammingNorm h = w - 6 ∧ (Function.support g \ Function.support h).ncard = 3)) :
    IsWeight 7 14 w := by
  obtain ⟨N, hparam⟩ := exists_directionBound w hw
  have hw6 : 6 ≤ w := (directionBounds_data (w, N) hparam).2.1
  obtain ⟨h, hh, g, hg, hcases⟩ := hdata
  refine ⟨combine g h, combine_mem_RM g h hg hh, ?_⟩
  rw [weight_combine]
  rcases hcases with ⟨hweight, hsupport⟩ | ⟨hweight, hsupport⟩
  · rw [hweight, hsupport]
    omega
  · rw [hweight, hsupport]
    omega

/-- The complete unchanged frozen proposition: existence equivalence and all direction lower bounds. -/
theorem propF : BackfillPaper6.V3.PropF := by
  constructor
  · intro w hw
    exact ⟨forward_criterion w hw, reverse_criterion w hw⟩
  · intro f hf w N hparam hw
    exact direction_bound f hf w N hparam hw

/-- Exact frozen contract check; this alias is not a separate mathematical result. -/
theorem check_PropF : BackfillPaper6.V3.PropF := propF

end Paper6DirectionCriterion

#print axioms Paper6DirectionCriterion.nonzeroDirections
#print axioms Paper6DirectionCriterion.goodDirections
#print axioms Paper6DirectionCriterion.card_nonzeroDirections
#print axioms Paper6DirectionCriterion.mem_goodDirections
#print axioms Paper6DirectionCriterion.good_direction_budget
#print axioms Paper6DirectionCriterion.directionBounds
#print axioms Paper6DirectionCriterion.directionBounds_data
#print axioms Paper6DirectionCriterion.exists_directionBound
#print axioms Paper6DirectionCriterion.good_card_lower_bound
#print axioms Paper6DirectionCriterion.decompAt_of_good
#print axioms Paper6DirectionCriterion.good_card_le_decomp_ncard
#print axioms Paper6DirectionCriterion.direction_bound
#print axioms Paper6DirectionCriterion.forward_criterion
#print axioms Paper6DirectionCriterion.combine
#print axioms Paper6DirectionCriterion.half0_combine
#print axioms Paper6DirectionCriterion.half1_combine
#print axioms Paper6DirectionCriterion.binary_cancel
#print axioms Paper6DirectionCriterion.delta_combine
#print axioms Paper6DirectionCriterion.combine_mem_RM
#print axioms Paper6DirectionCriterion.weight_combine
#print axioms Paper6DirectionCriterion.reverse_criterion
#print axioms Paper6DirectionCriterion.propF
#print axioms Paper6DirectionCriterion.check_PropF
#print Paper6DirectionCriterion.check_PropF
