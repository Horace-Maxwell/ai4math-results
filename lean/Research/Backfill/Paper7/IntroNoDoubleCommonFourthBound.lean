import Research.Backfill.Paper7.IntroUnicyclicInvisibleFourthMoment

/-! Without an off-diagonal pair of common neighbors, triangle-freeness
leaves at most one unit of fourth-moment mass at each nonneighbor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourCycleBridge
open Matrix SimpleGraph Paper7IntroTwoWalkCollision Paper7IntroPendantFour

theorem fourth_moment_upper_of_no_double_common_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (v : V)
    (hcommon : ∀ j, j ≠ v →
      ((G.neighborFinset v).filter (fun a => G.Adj a j)).card ≤ 1) :
    ((G.adjMatrix ℝ) ^ 4) v v ≤
      (G.degree v : ℝ) ^ 2 + Fintype.card V - (G.degree v : ℝ) - 1 := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) v v = (G.degree v : ℝ)
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hsq (j : V) (hj : j ≠ v) : ((A ^ 2) v j) ^ 2 ≤ 1 := by
    have hn : 0 ≤ (A ^ 2) v j := by
      change 0 ≤ ((G.adjMatrix ℝ) ^ 2) v j
      rw [adjacency_square_common_card]
      positivity
    have hh : (A ^ 2) v j ≤ 1 := by
      change ((G.adjMatrix ℝ) ^ 2) v j ≤ 1
      rw [adjacency_square_common_card]
      exact_mod_cast hcommon j hj
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]
  have hp (j : V) : ((A ^ 2) v j) ^ 2 + A v j ≤
      1 + (if j = v then (G.degree v : ℝ) ^ 2 - 1 else 0) := by
    by_cases hj : j = v
    · subst j
      have ha : A v v = 0 := by simp [A]
      rw [hdiag, ha, ite_eq_left rfl]
      nlinarith
    · rw [ite_eq_right hj]
      by_cases hvj : G.Adj v j
      · have hz : (A ^ 2) v j = 0 := triangle_free_square_neighbor_zero G htriangle v j hvj
        have ha : A v j = 1 := by simp [A, hvj]
        rw [hz, ha]
        norm_num
      · have ha : A v j = 0 := by simp [A, hvj]
        rw [ha]
        linarith [hsq j hj]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  have hfour : (A ^ 4) v v = ∑ j, ((A ^ 2) v j) ^ 2 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hA.pow 2).apply v j]
    ring
  have hrow : (∑ j, A v j) = (G.degree v : ℝ) := by
    simpa only [dotProduct, mul_one, Finset.sum_const,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul] using
      (G.adjMatrix_dotProduct (α := ℝ) v (fun _ => 1))
  have hright : (∑ j : V, ((1 : ℝ) +
      (if j = v then (G.degree v : ℝ) ^ 2 - 1 else 0))) =
      (Fintype.card V : ℝ) + ((G.degree v : ℝ) ^ 2 - 1) := by
    simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, ← hfour, hrow, hright] at hsum
  change (A ^ 4) v v ≤ (G.degree v : ℝ) ^ 2 + Fintype.card V - (G.degree v : ℝ) - 1
  linarith
#print axioms Paper7IntroFourCycleBridge.fourth_moment_upper_of_no_double_common_neighbors

end Paper7IntroFourCycleBridge
