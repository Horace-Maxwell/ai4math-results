import Research.Backfill.Paper7.IntroFourthMomentNeighborLower

/-! Exact fourth moments from actual zero/one off-diagonal two-walk counts,
or one actual off-diagonal two with all other entries zero/one.
These are generic identities, not assumptions of an original graph wrapper. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroExactFourthMoment
open Matrix SimpleGraph Paper7IntroCycleMomentLower

theorem fourth_moment_binary_off_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbinary : ∀ j, j ≠ v →
      ((G.adjMatrix ℝ) ^ 2) v j = 0 ∨ ((G.adjMatrix ℝ) ^ 2) v j = 1) :
    ((G.adjMatrix ℝ) ^ 4) v v = (G.degree v : ℝ) ^ 2 +
      ∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1) := by
  let A := G.adjMatrix ℝ
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) v v = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hp (j : V) : ((A ^ 2) v j) ^ 2 = (A ^ 2) v j +
      (if j = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) := by
    by_cases hj : j = v
    · subst j
      rw [hdiag, ite_eq_left rfl]
      ring
    · rw [ite_eq_right hj, add_zero]
      rcases hbinary j hj with h | h
      · change (((G.adjMatrix ℝ) ^ 2) v j) ^ 2 = ((G.adjMatrix ℝ) ^ 2) v j
        norm_num only [h]
      · change (((G.adjMatrix ℝ) ^ 2) v j) ^ 2 = ((G.adjMatrix ℝ) ^ 2) v j
        norm_num only [h]
  have hfour : (A ^ 4) v v = ∑ j : V, ((A ^ 2) v j) ^ 2 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _hj
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
  have hsum : (∑ j : V, ((A ^ 2) v j) ^ 2) =
      ∑ j : V, ((A ^ 2) v j +
        (if j = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0)) :=
    Finset.sum_congr rfl (fun j _hj => hp j)
  rw [Finset.sum_add_distrib, hrow, hbonus, ← hfour] at hsum
  change (A ^ 4) v v = (G.degree v : ℝ) ^ 2 + _
  rw [hexcess]
  linarith only [hsum]
#print axioms Paper7IntroExactFourthMoment.fourth_moment_binary_off_diagonal

theorem fourth_moment_one_double_off_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v j₀ : V) (hj₀ : j₀ ≠ v)
    (hdouble : ((G.adjMatrix ℝ) ^ 2) v j₀ = 2)
    (hbinary : ∀ j, j ≠ v → j ≠ j₀ →
      ((G.adjMatrix ℝ) ^ 2) v j = 0 ∨ ((G.adjMatrix ℝ) ^ 2) v j = 1) :
    ((G.adjMatrix ℝ) ^ 4) v v = (G.degree v : ℝ) ^ 2 +
      (∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1)) + 2 := by
  let A := G.adjMatrix ℝ
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) v v = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hp (j : V) : ((A ^ 2) v j) ^ 2 = (A ^ 2) v j +
      (if j = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) +
      (if j = j₀ then (2 : ℝ) else 0) := by
    by_cases hj : j = v
    · subst j
      rw [hdiag, ite_eq_left rfl, ite_eq_right hj₀.symm]
      ring
    · by_cases hj' : j = j₀
      · subst j
        change (((G.adjMatrix ℝ) ^ 2) v j₀) ^ 2 =
          ((G.adjMatrix ℝ) ^ 2) v j₀ +
          (if j₀ = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) +
          (if j₀ = j₀ then (2 : ℝ) else 0)
        norm_num [hdouble, hj₀]
      · rw [ite_eq_right hj, ite_eq_right hj', add_zero, add_zero]
        rcases hbinary j hj hj' with h | h
        · change (((G.adjMatrix ℝ) ^ 2) v j) ^ 2 = ((G.adjMatrix ℝ) ^ 2) v j
          norm_num only [h]
        · change (((G.adjMatrix ℝ) ^ 2) v j) ^ 2 = ((G.adjMatrix ℝ) ^ 2) v j
          norm_num only [h]
  have hfour : (A ^ 4) v v = ∑ j : V, ((A ^ 2) v j) ^ 2 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [(G.isSymm_adjMatrix.pow 2).apply v j]
    ring
  have hrow : (∑ j : V, (A ^ 2) v j) =
      ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := adjacency_square_row_sum G v
  have hbonus : (∑ j : V, if j = v then
      (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) =
        (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) := by simp
  have hmarked : (∑ j : V, if j = j₀ then (2 : ℝ) else 0) = 2 := by simp
  have hexcess : (∑ u ∈ G.neighborFinset v, ((G.degree u : ℝ) - 1)) =
      (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) - (G.degree v : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, mul_one]
  have hsum : (∑ j : V, ((A ^ 2) v j) ^ 2) =
      ∑ j : V, ((A ^ 2) v j +
        (if j = v then (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) else 0) +
        (if j = j₀ then (2 : ℝ) else 0)) :=
    Finset.sum_congr rfl (fun j _hj => hp j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hrow, hbonus, hmarked,
    ← hfour] at hsum
  change (A ^ 4) v v = (G.degree v : ℝ) ^ 2 + _ + 2
  rw [hexcess]
  linarith only [hsum]
#print axioms Paper7IntroExactFourthMoment.fourth_moment_one_double_off_diagonal

end Paper7IntroExactFourthMoment
