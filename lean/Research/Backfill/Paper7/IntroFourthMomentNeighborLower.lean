import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! Actual two-walk counts give a universal fourth-moment lower bound.
Repeated endpoints are counted with their full multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroCycleMomentLower
open Matrix SimpleGraph Paper7IntroPendantFour

theorem adjacency_square_row_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ j : V, ((G.adjMatrix ℝ) ^ 2) v j) =
      ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
  calc
    (∑ j : V, ((G.adjMatrix ℝ) ^ 2) v j) =
        ∑ j : V, ∑ u ∈ G.neighborFinset v, G.adjMatrix ℝ u j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_two, G.adjMatrix_mul_apply]
    _ = ∑ u ∈ G.neighborFinset v, ∑ j : V, G.adjMatrix ℝ u j := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u _
      simpa only [dotProduct, mul_one, Finset.sum_const,
        SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul] using
        (G.adjMatrix_dotProduct (α := ℝ) u (fun _ => 1))
#print axioms Paper7IntroCycleMomentLower.adjacency_square_row_sum

theorem fourth_moment_neighbor_excess_lower
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.degree v : ℝ) ^ 2 +
      (∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1)) ≤
        ((G.adjMatrix ℝ) ^ 4) v v := by
  let A := G.adjMatrix ℝ
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) v v = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hcount (j : V) : (A ^ 2) v j ≤ ((A ^ 2) v j) ^ 2 := by
    change ((G.adjMatrix ℝ) ^ 2) v j ≤ (((G.adjMatrix ℝ) ^ 2) v j) ^ 2
    rw [adjacency_square_common_card, pow_two]
    exact_mod_cast Nat.le_mul_self ((G.neighborFinset v).filter (fun u => G.Adj u j)).card
  have hp (j : V) : (A ^ 2) v j +
      (if j = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) ≤
        ((A ^ 2) v j) ^ 2 := by
    by_cases hj : j = v
    · subst j
      rw [hdiag, ite_eq_left rfl]
      linarith
    · rw [ite_eq_right hj, add_zero]
      exact hcount j
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  have hfour : (A ^ 4) v v = ∑ j : V, ((A ^ 2) v j) ^ 2 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [(G.isSymm_adjMatrix.pow 2).apply v j]
    ring
  have hrow : (∑ j : V, (A ^ 2) v j) =
      ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := adjacency_square_row_sum G v
  have hbonus : (∑ j : V, if j = v then
      (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) =
        (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) := by simp
  have hexcess : (∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1)) =
      (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) - (G.degree v : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, mul_one]
  rw [Finset.sum_add_distrib, hrow, hbonus, ← hfour] at hsum
  change (G.degree v : ℝ) ^ 2 +
    (∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1)) ≤ (A ^ 4) v v
  rw [hexcess]
  linarith
#print axioms Paper7IntroCycleMomentLower.fourth_moment_neighbor_excess_lower

end Paper7IntroCycleMomentLower
