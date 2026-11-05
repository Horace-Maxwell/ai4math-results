import Mathlib

/-! Source-only finite overlap budget and analytic contradictions for the
three-leaf, degree-three route. These are generic helpers; no original graph
exclusion or graph transport is claimed. The sealed hand route is jointly due
to Root and graph_shortarms_structure_1713. m3_degree_three_budget_2337 writes
the Lean candidate and its static package. -/
set_option autoImplicit false
noncomputable section
namespace Paper7ThreeLeafDegreeThreeBudget
open scoped BigOperators Classical

/-- Two subsets of a finite positive-weight budget can count one overlap twice. -/
theorem two_neighborhood_square_budget {α : Type*}
    (P Q R : Finset α) (h : α → ℝ)
    (hPR : P ⊆ R) (hQR : Q ⊆ R)
    (hpos : ∀ a ∈ R, 1 ≤ h a) (hoverlap : (P ∩ Q).card ≤ 1) :
    ∃ H : ℝ, 0 ≤ H ∧ H ^ 2 ≤ ∑ a ∈ R, (h a) ^ 2 ∧
      (∑ a ∈ P, h a) + (∑ a ∈ Q, h a) ≤ (∑ a ∈ R, (h a) ^ 2) + H := by
  have hIR : P ∩ Q ⊆ R := fun a ha => hPR (Finset.mem_inter.mp ha).1
  have hUR : P ∪ Q ⊆ R := by
    intro a ha
    rcases Finset.mem_union.mp ha with hp | hq
    · exact hPR hp
    · exact hQR hq
  have hnonneg : 0 ≤ ∑ a ∈ P ∩ Q, h a := by
    apply Finset.sum_nonneg
    intro a ha
    linarith only [hpos a (hIR ha)]
  have hsquare : (∑ a ∈ P ∩ Q, h a) ^ 2 ≤ ∑ a ∈ R, (h a) ^ 2 := by
    by_cases hempty : P ∩ Q = ∅
    · simpa only [hempty, Finset.sum_empty, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
        (Finset.sum_nonneg (s := R) (fun a _ha => sq_nonneg (h a)))
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hsingle : P ∩ Q = {a} := by
        ext b
        constructor
        · intro hb
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hoverlap b hb a ha)
        · intro hb
          have hba := Finset.mem_singleton.mp hb
          simpa only [hba] using ha
      rw [hsingle, Finset.sum_singleton]
      exact Finset.single_le_sum (fun b _hb => sq_nonneg (h b)) (hIR ha)
  have hlinear : (∑ a ∈ P ∪ Q, h a) ≤ ∑ a ∈ R, (h a) ^ 2 := by
    calc
      (∑ a ∈ P ∪ Q, h a) ≤ ∑ a ∈ P ∪ Q, (h a) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hge := hpos a (hUR ha)
        nlinarith
      _ ≤ ∑ a ∈ R, (h a) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hUR (fun a _ha _hna => sq_nonneg (h a))
  refine ⟨∑ a ∈ P ∩ Q, h a, hnonneg, hsquare, ?_⟩
  have hsplit : (∑ a ∈ P ∪ Q, h a) + (∑ a ∈ P ∩ Q, h a) =
      (∑ a ∈ P, h a) + (∑ a ∈ Q, h a) := Finset.sum_union_inter
  linarith only [hlinear, hsplit]
#print axioms Paper7ThreeLeafDegreeThreeBudget.two_neighborhood_square_budget

/-- The non-four-cycle scalar budget is impossible, even for real x and y. -/
theorem nonfour_scalar_contradiction (x y k H : ℝ)
    (hxy : x ≤ y) (hsum : x + y = 5) (hk : 0 ≤ k)
    (hH : 0 ≤ H) (hHs : H ^ 2 ≤ 2 * x * y - 6)
    (hE : 6 * x - 2 + k * (y - x) ≤ 2 * x * y - 6 + H) : False := by
  let r : ℝ := x - 1
  let D : ℝ := 2 * r ^ 2 + 2
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hprod : 0 ≤ k * (y - x) := mul_nonneg hk (sub_nonneg.mpr hxy)
  have hgap : 6 * x - 2 - (2 * x * y - 6) = D := by
    have hy : y = 5 - x := by linarith only [hsum]
    rw [hy]
    dsimp [D, r]
    ring
  have hDH : D ≤ H := by linarith only [hE, hprod, hgap]
  have hDsq : D ^ 2 ≤ H ^ 2 := by
    have hmul : 0 ≤ (H - D) * (H + D) :=
      mul_nonneg (sub_nonneg.mpr hDH) (by linarith only [hH, hDpos])
    nlinarith only [hmul]
  have hid : 10 * (D ^ 2 - (2 * x * y - 6)) =
      40 * r ^ 4 + (10 * r - 3) ^ 2 + 11 := by
    have hy : y = 5 - x := by linarith only [hsum]
    rw [hy]
    dsimp [D, r]
    ring
  have hstrict : 2 * x * y - 6 < D ^ 2 := by
    nlinarith only [hid, sq_nonneg (10 * r - 3), sq_nonneg (r ^ 2)]
  linarith only [hHs, hDsq, hstrict]
#print axioms Paper7ThreeLeafDegreeThreeBudget.nonfour_scalar_contradiction

/-- The four-cycle linear identity contradicts positive integer circle weights. -/
theorem four_cycle_integer_contradiction (x y k : ℤ)
    (hx : 0 < x) (hy : 0 < y) (hsum : x + y = 5)
    (hidentity : 14 * x - 25 = 5 * k) : False := by
  omega
#print axioms Paper7ThreeLeafDegreeThreeBudget.four_cycle_integer_contradiction

end Paper7ThreeLeafDegreeThreeBudget
