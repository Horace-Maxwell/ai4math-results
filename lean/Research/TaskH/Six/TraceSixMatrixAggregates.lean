import Research.TaskH.Six.TraceSixMatrixCommon

/-! Actual graph degree moments and weighted adjacency-power aggregates. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V]

theorem trace_symmetric_weighted_sum (K : V → V → ℝ)
    (hK : ∀ a v, K a v = K v a) (F : V → ℝ) :
    (∑ a : V, ∑ v : V, F v * K a v) =
      ∑ a : V, ∑ v : V, F a * K a v := by
  calc
    _ = ∑ v : V, ∑ a : V, F v * K a v := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      rw [hK v a]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_neighbor_degree_sum_total :
    (∑ a : V, ∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) = traceDegreeMoment G 2 := by
  calc
    _ = ∑ a : V, ∑ x : V, G.adjMatrix ℝ a x * (G.degree x : ℝ) :=
      Finset.sum_congr rfl (fun a _ =>
        (trace_adjacency_weighted_row_sum a (fun x => (G.degree x : ℝ))).symm)
    _ = ∑ x : V, ∑ a : V, G.adjMatrix ℝ a x * (G.degree x : ℝ) := Finset.sum_comm
    _ = ∑ x : V, (G.degree x : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, trace_adjacency_column_sum, pow_two]
    _ = _ := rfl

theorem trace_degree_neighbor_product_sum :
    (∑ a : V, (G.degree a : ℝ) * ∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) =
      traceOrderedDegreeProduct G := by
  simp only [Finset.mul_sum, traceOrderedDegreeProduct]

theorem trace_weighted_common_choose_moment_formula :
    4 * traceWeightedCommonChoose G =
      2 * (∑ a : V, ((G.degree a : ℝ) - 2) * traceAdjacencyPower G 4 a a) -
        2 * traceDegreeMoment G 3 + 10 * traceDegreeMoment G 2 -
          4 * traceDegreeMoment G 1 - 2 * traceOrderedDegreeProduct G := by
  have he : 4 * traceWeightedCommonChoose G =
      ∑ a : V, (2 * (((G.degree a : ℝ) - 2) * traceAdjacencyPower G 4 a a) -
        2 * (G.degree a : ℝ) ^ 3 + 6 * (G.degree a : ℝ) ^ 2 -
          2 * ((G.degree a : ℝ) * ∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) +
            4 * (∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) - 4 * (G.degree a : ℝ)) := by
    rw [trace_weighted_common_choose_matrix_formula, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  rw [trace_degree_neighbor_product_sum, trace_neighbor_degree_sum_total] at he
  have hh : 4 * traceWeightedCommonChoose G =
      2 * (∑ a : V, ((G.degree a : ℝ) - 2) * traceAdjacencyPower G 4 a a) -
        2 * traceDegreeMoment G 3 + 6 * traceDegreeMoment G 2 -
          2 * traceOrderedDegreeProduct G + 4 * traceDegreeMoment G 2 -
            4 * traceDegreeMoment G 1 := by
    simpa only [traceDegreeMoment, pow_one] using he
  linarith

theorem trace_cube_dot_row (a : V) :
    (∑ v : V, G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) =
      traceAdjacencyPower G 4 a a := by
  classical
  calc
    _ = ∑ v : V, G.adjMatrix ℝ a v * traceAdjacencyPower G 3 v a := by
      apply Finset.sum_congr rfl
      intro v _
      rw [trace_adjacency_power_symm 3 a v]
    _ = _ := by
      change (G.adjMatrix ℝ * (G.adjMatrix ℝ ^ 3)) a a = (G.adjMatrix ℝ ^ 4) a a
      rw [← pow_succ']

theorem trace_cube_edge_degree_cross :
    (∑ a : V, ∑ v : V,
      ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) *
        G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) =
      ∑ a : V, (2 * (G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a := by
  let K : V → V → ℝ := fun a v => G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v
  have hK (a v : V) : K a v = K v a := by
    change G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v =
      G.adjMatrix ℝ v a * traceAdjacencyPower G 3 v a
    exact congrArg₂ (fun (x y : ℝ) => x * y)
      ((G.isSymm_adjMatrix (α := ℝ)).apply v a) (trace_adjacency_power_symm 3 a v)
  have hswap := trace_symmetric_weighted_sum K hK (fun a => (G.degree a : ℝ))
  have hrow (a : V) : (∑ v : V, K a v) = traceAdjacencyPower G 4 a a :=
    trace_cube_dot_row a
  calc
    _ = ∑ a : V, ∑ v : V,
        ((G.degree a : ℝ) * K a v + (G.degree v : ℝ) * K a v - K a v) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      dsimp [K]
      ring
    _ = (∑ a : V, ∑ v : V, (G.degree a : ℝ) * K a v) +
        (∑ a : V, ∑ v : V, (G.degree v : ℝ) * K a v) -
          ∑ a : V, ∑ v : V, K a v := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ a : V, (G.degree a : ℝ) * traceAdjacencyPower G 4 a a) +
        (∑ a : V, (G.degree a : ℝ) * traceAdjacencyPower G 4 a a) -
          ∑ a : V, traceAdjacencyPower G 4 a a := by
      rw [hswap]
      simp only [← Finset.mul_sum, hrow]
    _ = _ := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem trace_adjacency_left_moment_sum (r : ℕ) :
    (∑ a : V, ∑ v : V, (G.degree a : ℝ) ^ r * G.adjMatrix ℝ a v) =
      traceDegreeMoment G (r + 1) := by
  unfold traceDegreeMoment
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, trace_adjacency_row_sum, pow_succ]

theorem trace_adjacency_right_moment_sum (r : ℕ) :
    (∑ a : V, ∑ v : V, (G.degree v : ℝ) ^ r * G.adjMatrix ℝ a v) =
      traceDegreeMoment G (r + 1) := by
  have hs := trace_symmetric_weighted_sum (fun a v => G.adjMatrix ℝ a v)
    (fun a v => (G.isSymm_adjMatrix (α := ℝ)).apply v a)
    (fun a => (G.degree a : ℝ) ^ r)
  rw [hs, trace_adjacency_left_moment_sum]

theorem trace_adjacency_degree_product_sum :
    (∑ a : V, ∑ v : V, (G.degree a : ℝ) * (G.degree v : ℝ) * G.adjMatrix ℝ a v) =
      traceOrderedDegreeProduct G := by
  calc
    _ = ∑ a : V, ∑ v : V,
        G.adjMatrix ℝ a v * ((G.degree a : ℝ) * (G.degree v : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      unfold traceOrderedDegreeProduct
      exact Finset.sum_congr rfl (fun a _ => trace_adjacency_weighted_row_sum a
        (fun v => (G.degree a : ℝ) * (G.degree v : ℝ)))

theorem trace_adjacency_linear_correction_sum :
    (∑ a : V, ∑ v : V,
      ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) =
      2 * traceDegreeMoment G 2 - traceDegreeMoment G 1 := by
  have hL : (∑ a : V, ∑ v : V, (G.degree a : ℝ) * G.adjMatrix ℝ a v) =
      traceDegreeMoment G 2 := by
    simpa only [pow_one] using trace_adjacency_left_moment_sum (G := G) 1
  have hR : (∑ a : V, ∑ v : V, (G.degree v : ℝ) * G.adjMatrix ℝ a v) =
      traceDegreeMoment G 2 := by
    simpa only [pow_one] using trace_adjacency_right_moment_sum (G := G) 1
  have h0 : (∑ a : V, ∑ v : V, G.adjMatrix ℝ a v) = traceDegreeMoment G 1 := by
    simpa only [pow_zero, one_mul] using trace_adjacency_left_moment_sum (G := G) 0
  calc
    _ = (∑ a : V, ∑ v : V, (G.degree a : ℝ) * G.adjMatrix ℝ a v) +
        (∑ a : V, ∑ v : V, (G.degree v : ℝ) * G.adjMatrix ℝ a v) -
          ∑ a : V, ∑ v : V, G.adjMatrix ℝ a v := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by rw [hL, hR, h0]; ring

theorem trace_adjacency_square_correction_sum :
    (∑ a : V, ∑ v : V,
      ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) ^ 2 * G.adjMatrix ℝ a v) =
      2 * traceDegreeMoment G 3 - 4 * traceDegreeMoment G 2 +
        traceDegreeMoment G 1 + 2 * traceOrderedDegreeProduct G := by
  have hL := trace_adjacency_left_moment_sum (G := G) 2
  have hR := trace_adjacency_right_moment_sum (G := G) 2
  have hL1 : (∑ a : V, ∑ v : V, (G.degree a : ℝ) * G.adjMatrix ℝ a v) =
      traceDegreeMoment G 2 := by
    simpa only [pow_one] using trace_adjacency_left_moment_sum (G := G) 1
  have hR1 : (∑ a : V, ∑ v : V, (G.degree v : ℝ) * G.adjMatrix ℝ a v) =
      traceDegreeMoment G 2 := by
    simpa only [pow_one] using trace_adjacency_right_moment_sum (G := G) 1
  have h0 : (∑ a : V, ∑ v : V, G.adjMatrix ℝ a v) = traceDegreeMoment G 1 := by
    simpa only [pow_zero, one_mul] using trace_adjacency_left_moment_sum (G := G) 0
  calc
    _ = ∑ a : V, ∑ v : V,
        ((G.degree a : ℝ) ^ 2 * G.adjMatrix ℝ a v +
          (G.degree v : ℝ) ^ 2 * G.adjMatrix ℝ a v + G.adjMatrix ℝ a v +
            2 * ((G.degree a : ℝ) * (G.degree v : ℝ) * G.adjMatrix ℝ a v) -
              2 * ((G.degree a : ℝ) * G.adjMatrix ℝ a v) -
                2 * ((G.degree v : ℝ) * G.adjMatrix ℝ a v)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (∑ a : V, ∑ v : V, (G.degree a : ℝ) ^ 2 * G.adjMatrix ℝ a v) +
        (∑ a : V, ∑ v : V, (G.degree v : ℝ) ^ 2 * G.adjMatrix ℝ a v) +
          (∑ a : V, ∑ v : V, G.adjMatrix ℝ a v) +
            2 * (∑ a : V, ∑ v : V,
              (G.degree a : ℝ) * (G.degree v : ℝ) * G.adjMatrix ℝ a v) -
                2 * (∑ a : V, ∑ v : V, (G.degree a : ℝ) * G.adjMatrix ℝ a v) -
                  2 * (∑ a : V, ∑ v : V, (G.degree v : ℝ) * G.adjMatrix ℝ a v) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      rw [hL, hR, h0, trace_adjacency_degree_product_sum, hL1, hR1]
      ring

end TaskH.Six

#print axioms TaskH.Six.trace_symmetric_weighted_sum
#print axioms TaskH.Six.trace_neighbor_degree_sum_total
#print axioms TaskH.Six.trace_degree_neighbor_product_sum
#print axioms TaskH.Six.trace_weighted_common_choose_moment_formula
#print axioms TaskH.Six.trace_cube_dot_row
#print axioms TaskH.Six.trace_cube_edge_degree_cross
#print axioms TaskH.Six.trace_adjacency_left_moment_sum
#print axioms TaskH.Six.trace_adjacency_right_moment_sum
#print axioms TaskH.Six.trace_adjacency_degree_product_sum
#print axioms TaskH.Six.trace_adjacency_linear_correction_sum
#print axioms TaskH.Six.trace_adjacency_square_correction_sum
