import Research.Backfill.Paper7.IntroPendantFourMoments

/-! A local fourth-moment bound at every vertex all of whose incident edges
are bridges. It applies to arbitrary branching and needs no tree catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPendantFour
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem bridge_vertex_common_neighbor_unique
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a))
    (j : V) (hj : j ≠ v) (a b : V)
    (hva : G.Adj v a) (haj : G.Adj a j)
    (hvb : G.Adj v b) (hbj : G.Adj b j) : a = b := by
  by_contra hab
  let T := G.deleteEdges ({s(v, a)} : Set (Sym2 V))
  have h1 : T.Adj v b := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hvb, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact hab h.symm
    · exact hva.ne h
  have h2 : T.Adj b j := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hbj, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hvb.ne h.symm
    · exact hab h.symm
  have h3 : T.Adj j a := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨haj.symm, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hj h
    · exact hva.ne h.symm
  exact (SimpleGraph.isBridge_iff.mp (hbridge a hva))
    (h1.reachable.trans (h2.reachable.trans h3.reachable))
#print axioms Paper7IntroPendantFour.bridge_vertex_common_neighbor_unique

theorem bridge_vertex_no_neighbor_triangle
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a))
    (j a : V) (hvj : G.Adj v j) (hva : G.Adj v a) (haj : G.Adj a j) : False := by
  let T := G.deleteEdges ({s(v, j)} : Set (Sym2 V))
  have h1 : T.Adj v a := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hva, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact haj.ne h
    · exact hvj.ne h
  have h2 : T.Adj a j := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨haj, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hva.ne h.symm
    · exact haj.ne h
  exact (SimpleGraph.isBridge_iff.mp (hbridge j hvj)) (h1.reachable.trans h2.reachable)
#print axioms Paper7IntroPendantFour.bridge_vertex_no_neighbor_triangle

theorem adjacency_square_common_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v j : V) :
    ((G.adjMatrix ℝ) ^ 2) v j =
      (((G.neighborFinset v).filter (fun a => G.Adj a j)).card : ℝ) := by
  rw [pow_two, G.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one]
#print axioms Paper7IntroPendantFour.adjacency_square_common_card

theorem bridge_vertex_square_offdiag_zero_or_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a)) (j : V) (hj : j ≠ v) :
    ((G.adjMatrix ℝ) ^ 2) v j = 0 ∨ ((G.adjMatrix ℝ) ^ 2) v j = 1 := by
  have hc : ((G.neighborFinset v).filter (fun a => G.Adj a j)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    exact bridge_vertex_common_neighbor_unique G v hbridge j hj a b
      ((G.mem_neighborFinset v a).mp ha1) ha2 ((G.mem_neighborFinset v b).mp hb1) hb2
  have he : ((G.neighborFinset v).filter (fun a => G.Adj a j)).card = 0 ∨
      ((G.neighborFinset v).filter (fun a => G.Adj a j)).card = 1 := by omega
  rw [adjacency_square_common_card]
  rcases he with h | h
  · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inr (by rw [h]; norm_num)
#print axioms Paper7IntroPendantFour.bridge_vertex_square_offdiag_zero_or_one

theorem bridge_vertex_square_neighbor_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a)) (j : V) (hj : G.Adj v j) :
    ((G.adjMatrix ℝ) ^ 2) v j = 0 := by
  have he : (G.neighborFinset v).filter (fun a => G.Adj a j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    exact bridge_vertex_no_neighbor_triangle G v hbridge j a hj
      ((G.mem_neighborFinset v a).mp ha1) ha2
  rw [adjacency_square_common_card, he]
  norm_num
#print axioms Paper7IntroPendantFour.bridge_vertex_square_neighbor_zero

theorem bridge_vertex_fourth_moment_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hbridge : ∀ a, G.Adj v a → G.IsBridge s(v, a)) :
    ((G.adjMatrix ℝ) ^ 4) v v + (G.degree v : ℝ) + 1 ≤
      (G.degree v : ℝ) ^ 2 + Fintype.card V := by
  let A := G.adjMatrix ℝ
  have hdiag : (A ^ 2) v v = (G.degree v : ℝ) := by
    simpa only [A, pow_two] using (G.adjMatrix_mul_self_apply_self (α := ℝ) v)
  have hp (j : V) : ((A ^ 2) v j) ^ 2 + A v j ≤
      1 + (if j = v then (G.degree v : ℝ) ^ 2 - 1 else 0) := by
    by_cases hj : j = v
    · subst j
      rw [hdiag]
      have hz : A v v = 0 := by simp [A]
      rw [hz, ite_eq_left rfl]
      linarith
    · rw [ite_eq_right hj]
      by_cases hvj : G.Adj v j
      · have hz := bridge_vertex_square_neighbor_zero G v hbridge j hvj
        have ha : A v j = 1 := by simp [A, hvj]
        rw [hz, ha]
        norm_num
      · have ha : A v j = 0 := by simp [A, hvj]
        rcases bridge_vertex_square_offdiag_zero_or_one G v hbridge j hj with h | h
        · rw [h, ha]; norm_num
        · rw [h, ha]; norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  have hfour : (A ^ 4) v v = ∑ j, ((A ^ 2) v j) ^ 2 := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [(G.isSymm_adjMatrix.pow 2).apply v j]
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
  linarith
#print axioms Paper7IntroPendantFour.bridge_vertex_fourth_moment_bound

end Paper7IntroPendantFour
