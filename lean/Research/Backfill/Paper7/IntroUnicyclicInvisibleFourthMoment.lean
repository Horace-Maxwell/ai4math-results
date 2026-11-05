import Research.Backfill.Paper7.IntroUnicyclicTwoWalkCollision
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! A fourth-moment vertex budget with an actual set of vertices invisible
to walks of length zero, one and two from the chosen root. The unique cycle
costs at most three in this local bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTwoWalkCollision
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7IntroPendantFour

theorem triangle_free_square_neighbor_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (v j : V) (hvj : G.Adj v j) : ((G.adjMatrix ℝ) ^ 2) v j = 0 := by
  have he : (G.neighborFinset v).filter (fun a => G.Adj a j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨haN, haj⟩ := Finset.mem_filter.mp ha
    exact htriangle v a j ((G.mem_neighborFinset v a).mp haN) haj hvj.symm
  rw [adjacency_square_common_card, he]
  norm_num
#print axioms Paper7IntroTwoWalkCollision.triangle_free_square_neighbor_zero

theorem unicyclic_fourth_moment_invisible_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (htriangle : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj k i → False)
    (v : V) (E : Finset V)
    (hE : ∀ j ∈ E, j ≠ v ∧ ¬G.Adj v j ∧ ((G.adjMatrix ℝ) ^ 2) v j = 0) :
    ((G.adjMatrix ℝ) ^ 4) v v + (G.degree v : ℝ) + 1 + E.card ≤
      (G.degree v : ℝ) ^ 2 + Fintype.card V + 3 := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  obtain ⟨q, hq⟩ := unicyclic_common_card_one_exception G b hG htriangle v
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    change ((G.adjMatrix ℝ) ^ 2) v v = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hsq (j : V) (hj : j ≠ v) :
      ((A ^ 2) v j) ^ 2 ≤ 1 + (if j = q then (3 : ℝ) else 0) := by
    have hn : 0 ≤ (A ^ 2) v j := by
      change 0 ≤ ((G.adjMatrix ℝ) ^ 2) v j
      rw [adjacency_square_common_card]
      positivity
    have hc := hq j hj
    by_cases hjq : j = q
    · rw [ite_eq_left hjq] at hc ⊢
      have hh : (A ^ 2) v j ≤ 2 := by
        change ((G.adjMatrix ℝ) ^ 2) v j ≤ 2
        rw [adjacency_square_common_card]
        exact_mod_cast hc
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]
    · rw [ite_eq_right hjq] at hc ⊢
      have hh : (A ^ 2) v j ≤ 1 := by
        change ((G.adjMatrix ℝ) ^ 2) v j ≤ 1
        rw [adjacency_square_common_card]
        exact_mod_cast hc
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]
  have hbonus (j : V) : 0 ≤ (if j = q then (3 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hp (j : V) : ((A ^ 2) v j) ^ 2 + A v j +
      (if j ∈ E then (1 : ℝ) else 0) ≤
      1 + (if j = v then (G.degree v : ℝ) ^ 2 - 1 else 0) +
        (if j = q then (3 : ℝ) else 0) := by
    by_cases hj : j = v
    · subst j
      have hvE : v ∉ E := fun h => (hE v h).1 rfl
      have ha : A v v = 0 := by simp [A]
      rw [hdiag, ha, ite_eq_right hvE, ite_eq_left rfl]
      linarith [hbonus v]
    · rw [ite_eq_right hj]
      by_cases hjE : j ∈ E
      · have hz : (A ^ 2) v j = 0 := (hE j hjE).2.2
        have ha : A v j = 0 := by simp [A, (hE j hjE).2.1]
        rw [ite_eq_left hjE, hz, ha]
        linarith [hbonus j]
      · rw [ite_eq_right hjE]
        by_cases hvj : G.Adj v j
        · have hz : (A ^ 2) v j = 0 := triangle_free_square_neighbor_zero G htriangle v j hvj
          have ha : A v j = 1 := by simp [A, hvj]
          rw [hz, ha]
          linarith [hbonus j]
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
  have hsumE : (∑ j : V, if j ∈ E then (1 : ℝ) else 0) = E.card := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun j : V => j ∈ E) = E := by ext j; simp
    rw [he]
    simp
  have hright : (∑ j : V, ((1 : ℝ) +
      (if j = v then (G.degree v : ℝ) ^ 2 - 1 else 0) +
      (if j = q then (3 : ℝ) else 0))) =
      (Fintype.card V : ℝ) + ((G.degree v : ℝ) ^ 2 - 1) + 3 := by
    simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hfour, hrow, hsumE, hright] at hsum
  change (A ^ 4) v v + (G.degree v : ℝ) + 1 + E.card ≤
    (G.degree v : ℝ) ^ 2 + Fintype.card V + 3
  linarith
#print axioms Paper7IntroTwoWalkCollision.unicyclic_fourth_moment_invisible_bound

end Paper7IntroTwoWalkCollision
