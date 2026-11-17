import Research.TaskH.Six.TraceSixMoments

/-! Actual adjacency-matrix sums and the scaled Frobenius lower bound. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V]

theorem trace_matrix_row_product_sum (M N : Matrix V V ℝ) (v : V) :
    (∑ w : V, (M * N) v w) = ∑ z : V, M v z * ∑ w : V, N z w := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem trace_matrix_product_entry_sum (M N : Matrix V V ℝ) :
    (∑ v : V, ∑ w : V, (M * N) v w) =
      ∑ z : V, (∑ v : V, M v z) * ∑ w : V, N z w := by
  calc
    _ = ∑ v : V, ∑ z : V, M v z * ∑ w : V, N z w :=
      Finset.sum_congr rfl (fun v _ => trace_matrix_row_product_sum M N v)
    _ = ∑ z : V, ∑ v : V, M v z * ∑ w : V, N z w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def traceAdjacencyPower (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) : Matrix V V ℝ := by
  classical
  exact G.adjMatrix ℝ ^ r

noncomputable def traceDefect (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun v w => traceAdjacencyPower G 3 v w -
    3 * ((G.degree v : ℝ) - 1) * G.adjMatrix ℝ v w

noncomputable def traceDefectSquare (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ v : V, ∑ w : V, (traceDefect G v w) ^ 2

theorem trace_adjacency_row_sum (v : V) :
    (∑ w : V, G.adjMatrix ℝ v w) = (G.degree v : ℝ) := by
  simpa only [Matrix.mulVec, dotProduct, Function.const, mul_one] using
    (SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (a := (1 : ℝ)) (v := v))

theorem trace_adjacency_column_sum (w : V) :
    (∑ v : V, G.adjMatrix ℝ v w) = (G.degree w : ℝ) := by
  calc
    _ = ∑ v : V, G.adjMatrix ℝ w v := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]
    _ = _ := trace_adjacency_row_sum w

theorem trace_adjacency_weighted_row_sum (v : V) (f : V → ℝ) :
    (∑ w : V, G.adjMatrix ℝ v w * f w) = ∑ w ∈ G.neighborFinset v, f w :=
  G.adjMatrix_dotProduct v f

theorem trace_adjacency_cube_entry_sum :
    (∑ v : V, ∑ w : V, traceAdjacencyPower G 3 v w) =
      traceOrderedDegreeProduct G := by
  classical
  have hpow : G.adjMatrix ℝ ^ 3 = G.adjMatrix ℝ * (G.adjMatrix ℝ * G.adjMatrix ℝ) := by
    rw [show (3 : ℕ) = 1 + 2 by decide, pow_add, pow_one, pow_two]
  calc
    _ = ∑ z : V, (∑ v : V, G.adjMatrix ℝ v z) *
        ∑ w : V, (G.adjMatrix ℝ * G.adjMatrix ℝ) z w := by
      rw [traceAdjacencyPower, hpow, trace_matrix_product_entry_sum]
    _ = ∑ z : V, (G.degree z : ℝ) *
        ∑ w : V, (G.adjMatrix ℝ * G.adjMatrix ℝ) z w := by
      simp only [trace_adjacency_column_sum]
    _ = ∑ z : V, (G.degree z : ℝ) *
        ∑ t : V, G.adjMatrix ℝ z t * (G.degree t : ℝ) := by
      simp only [trace_matrix_row_product_sum, trace_adjacency_row_sum]
    _ = ∑ z : V, (G.degree z : ℝ) * ∑ t ∈ G.neighborFinset z, (G.degree t : ℝ) := by
      simp only [trace_adjacency_weighted_row_sum]
    _ = _ := by simp only [traceOrderedDegreeProduct, Finset.mul_sum]

theorem trace_defect_entry_sum :
    (∑ v : V, ∑ w : V, traceDefect G v w) = traceOrderedDegreeProduct G -
      3 * traceDegreeMoment G 2 + 3 * traceDegreeMoment G 1 := by
  have hoff : (∑ v : V, ∑ w : V,
      3 * ((G.degree v : ℝ) - 1) * G.adjMatrix ℝ v w) =
      3 * traceDegreeMoment G 2 - 3 * traceDegreeMoment G 1 := by
    calc
      _ = ∑ v : V, 3 * ((G.degree v : ℝ) - 1) * (G.degree v : ℝ) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.mul_sum, trace_adjacency_row_sum]
      _ = ∑ v : V, (3 * (G.degree v : ℝ) ^ 2 - 3 * (G.degree v : ℝ)) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, traceDegreeMoment, pow_one]
  simp only [traceDefect, Finset.sum_sub_distrib]
  rw [trace_adjacency_cube_entry_sum, hoff]
  ring

omit [DecidableRel G.Adj] in
theorem trace_matrix_entry_cauchy (M : Matrix V V ℝ) :
    (∑ v : V, ∑ w : V, M v w) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * ∑ v : V, ∑ w : V, (M v w) ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V))
    (fun p => M p.1 p.2) (fun _ => (1 : ℝ))
  simpa [Fintype.sum_prod_type, pow_two, mul_comm] using hc

theorem trace_defect_cauchy :
    (∑ v : V, ∑ w : V, traceDefect G v w) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * traceDefectSquare G :=
  trace_matrix_entry_cauchy (traceDefect G)

theorem trace_defect_scaled_square_lower
    (hlo : ∀ v : V, 11 ≤ G.degree v) :
    (8 * traceDegreeMoment G 2 + 33 * (Fintype.card V : ℝ)) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * traceDefectSquare G := by
  have hq := trace_ordered_degree_product_lower hlo
  have h1 := trace_degree_first_moment_lower hlo
  have h2 := trace_degree_second_moment_lower hlo
  have hm := trace_defect_entry_sum (G := G)
  have hc := trace_defect_cauchy (G := G)
  have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hl : 0 ≤ 8 * traceDegreeMoment G 2 + 33 * (Fintype.card V : ℝ) := by
    nlinarith
  have he : 8 * traceDegreeMoment G 2 + 33 * (Fintype.card V : ℝ) ≤
      ∑ v : V, ∑ w : V, traceDefect G v w := by
    linarith
  have hs := mul_self_le_mul_self hl he
  nlinarith [hs]

theorem trace_defect_square_lower [Nonempty V]
    (hlo : ∀ v : V, 11 ≤ G.degree v) :
    (8 * (traceDegreeMoment G 2 / (Fintype.card V : ℝ)) + 33) ^ 2 ≤
      traceDefectSquare G := by
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (Fintype.card_pos (α := V))
  have hs := trace_defect_scaled_square_lower hlo
  have he : (8 * (traceDegreeMoment G 2 / (Fintype.card V : ℝ)) + 33) ^ 2 =
      (8 * traceDegreeMoment G 2 + 33 * (Fintype.card V : ℝ)) ^ 2 /
        (Fintype.card V : ℝ) ^ 2 := by
    field_simp [ne_of_gt hn]
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith [hs]

end TaskH.Six

#print axioms TaskH.Six.trace_matrix_row_product_sum
#print axioms TaskH.Six.trace_matrix_product_entry_sum
#print axioms TaskH.Six.trace_adjacency_row_sum
#print axioms TaskH.Six.trace_adjacency_column_sum
#print axioms TaskH.Six.trace_adjacency_weighted_row_sum
#print axioms TaskH.Six.trace_adjacency_cube_entry_sum
#print axioms TaskH.Six.trace_defect_entry_sum
#print axioms TaskH.Six.trace_matrix_entry_cauchy
#print axioms TaskH.Six.trace_defect_cauchy
#print axioms TaskH.Six.trace_defect_scaled_square_lower
#print axioms TaskH.Six.trace_defect_square_lower
