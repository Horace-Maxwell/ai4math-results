import Research.TaskH.Six.TraceSixMatrixAggregates

/-!
The actual simple-threepath first and second moments.  The off-diagonal
backtrack formula is used only off diagonal; diagonal triangle walks are
removed explicitly before the global matrix moments are combined.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem trace_adjacency_entry_sq (a v : V) :
    (G.adjMatrix ℝ a v) ^ 2 = G.adjMatrix ℝ a v := by
  by_cases hav : G.Adj a v <;> simp [SimpleGraph.adjMatrix_apply, hav]

open scoped Classical in
theorem trace_simple_path_entry (a v : V) :
    ((traceThreePaths G a v).card : ℝ) = if a ≠ v then
      traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v else 0 := by
  classical
  by_cases hav : a ≠ v
  · simpa only [ite_eq_left hav] using
      traceThreePaths_card_eq_adjacency_cube_corrected (G := G) a v hav
  · have he : a = v := not_ne_iff.mp hav
    subst v
    simp [traceThreePaths_self]

open scoped Classical in
theorem trace_simple_path_square_entry (a v : V) :
    (((traceThreePaths G a v).card : ℝ) ^ 2) = if a ≠ v then
      (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2 else 0 := by
  classical
  have hh := congrArg (fun x : ℝ => x ^ 2) (trace_simple_path_entry (G := G) a v)
  by_cases hav : a ≠ v
  · simpa only [ite_eq_left hav] using hh
  · simpa only [ite_eq_right hav, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hh

theorem trace_simple_path_row_sum (a : V) :
    (∑ v : V, ((traceThreePaths G a v).card : ℝ)) =
      (∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v)) -
          2 * traceLocalTriangleCount G a := by
  classical
  calc
    _ = ∑ v : V, if a ≠ v then
        traceAdjacencyPower G 3 a v -
          ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v else 0 :=
      Finset.sum_congr rfl (fun v _ => trace_simple_path_entry a v)
    _ = (∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v)) -
          (traceAdjacencyPower G 3 a a -
            ((G.degree a : ℝ) + (G.degree a : ℝ) - 1) * G.adjMatrix ℝ a a) :=
      trace_offdiagonal_sum _ a
    _ = _ := by
      have ha : G.adjMatrix ℝ a a = 0 := by simp
      simp only [ha, mul_zero, sub_zero, trace_cube_diagonal_triangle]

theorem trace_simple_path_row_square_sum (a : V) :
    (∑ v : V, ((traceThreePaths G a v).card : ℝ) ^ 2) =
      (∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2) -
          4 * (traceLocalTriangleCount G a : ℝ) ^ 2 := by
  classical
  calc
    _ = ∑ v : V, if a ≠ v then
        (traceAdjacencyPower G 3 a v -
          ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2 else 0 :=
      Finset.sum_congr rfl (fun v _ => trace_simple_path_square_entry a v)
    _ = (∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2) -
          (traceAdjacencyPower G 3 a a -
            ((G.degree a : ℝ) + (G.degree a : ℝ) - 1) * G.adjMatrix ℝ a a) ^ 2 :=
      trace_offdiagonal_sum _ a
    _ = _ := by
      have ha : G.adjMatrix ℝ a a = 0 := by simp
      rw [ha, trace_cube_diagonal_triangle]
      ring

theorem trace_simple_path_global_sum :
    (∑ a : V, ∑ v : V, ((traceThreePaths G a v).card : ℝ)) =
      traceOrderedDegreeProduct G - 2 * traceDegreeMoment G 2 +
        traceDegreeMoment G 1 - 2 * traceTriangleMoment G 1 := by
  calc
    _ = ∑ a : V, ((∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v)) -
          2 * traceLocalTriangleCount G a) :=
      Finset.sum_congr rfl (fun a _ => trace_simple_path_row_sum a)
    _ = (∑ a : V, ∑ v : V, traceAdjacencyPower G 3 a v) -
        (∑ a : V, ∑ v : V,
          ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) -
            2 * traceTriangleMoment G 1 := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, traceTriangleMoment, pow_one]
    _ = _ := by
      rw [trace_adjacency_cube_entry_sum, trace_adjacency_linear_correction_sum]
      ring

theorem trace_corrected_cube_square_sum :
    (∑ a : V, ∑ v : V, (traceAdjacencyPower G 3 a v -
      ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2) =
      (∑ a : V, traceAdjacencyPower G 6 a a) -
        2 * (∑ a : V, (2 * (G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
          2 * traceDegreeMoment G 3 - 4 * traceDegreeMoment G 2 +
            traceDegreeMoment G 1 + 2 * traceOrderedDegreeProduct G := by
  calc
    _ = ∑ a : V, ∑ v : V,
        ((traceAdjacencyPower G 3 a v) ^ 2 -
          2 * (((G.degree a : ℝ) + (G.degree v : ℝ) - 1) *
            G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) +
              ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) ^ 2 * G.adjMatrix ℝ a v) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      calc
        _ = (traceAdjacencyPower G 3 a v) ^ 2 -
            2 * (((G.degree a : ℝ) + (G.degree v : ℝ) - 1) *
              G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) +
                ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) ^ 2 * (G.adjMatrix ℝ a v) ^ 2 := by
          ring
        _ = _ := by rw [trace_adjacency_entry_sq]
    _ = (∑ a : V, ∑ v : V, (traceAdjacencyPower G 3 a v) ^ 2) -
        2 * (∑ a : V, ∑ v : V,
          ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) *
            G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) +
              ∑ a : V, ∑ v : V,
                ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) ^ 2 * G.adjMatrix ℝ a v := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [trace_sixth_diagonal_sum, trace_cube_edge_degree_cross,
        trace_adjacency_square_correction_sum]
      ring

theorem trace_simple_path_global_square_sum :
    (∑ a : V, ∑ v : V, ((traceThreePaths G a v).card : ℝ) ^ 2) =
      (∑ a : V, traceAdjacencyPower G 6 a a) -
        2 * (∑ a : V, (2 * (G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
          2 * traceDegreeMoment G 3 - 4 * traceDegreeMoment G 2 +
            traceDegreeMoment G 1 + 2 * traceOrderedDegreeProduct G -
              4 * traceTriangleMoment G 2 := by
  calc
    _ = ∑ a : V, ((∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2) -
          4 * (traceLocalTriangleCount G a : ℝ) ^ 2) :=
      Finset.sum_congr rfl (fun a _ => trace_simple_path_row_square_sum a)
    _ = (∑ a : V, ∑ v : V, (traceAdjacencyPower G 3 a v -
        ((G.degree a : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2) -
          4 * traceTriangleMoment G 2 := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, traceTriangleMoment]
    _ = _ := by rw [trace_corrected_cube_square_sum]

theorem trace_simple_path_pair_moment_formula :
    (∑ a : V, ∑ v : V,
      (((traceThreePaths G a v).card : ℝ) ^ 2 - (traceThreePaths G a v).card)) =
      (∑ a : V, traceAdjacencyPower G 6 a a) -
        2 * (∑ a : V, (2 * (G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
          2 * traceDegreeMoment G 3 - 2 * traceDegreeMoment G 2 +
            traceOrderedDegreeProduct G - 4 * traceTriangleMoment G 2 +
              2 * traceTriangleMoment G 1 := by
  simp only [Finset.sum_sub_distrib]
  rw [trace_simple_path_global_square_sum, trace_simple_path_global_sum]
  ring

end TaskH.Six

#print axioms TaskH.Six.trace_adjacency_entry_sq
#print axioms TaskH.Six.trace_simple_path_entry
#print axioms TaskH.Six.trace_simple_path_square_entry
#print axioms TaskH.Six.trace_simple_path_row_sum
#print axioms TaskH.Six.trace_simple_path_row_square_sum
#print axioms TaskH.Six.trace_simple_path_global_sum
#print axioms TaskH.Six.trace_corrected_cube_square_sum
#print axioms TaskH.Six.trace_simple_path_global_square_sum
#print axioms TaskH.Six.trace_simple_path_pair_moment_formula
