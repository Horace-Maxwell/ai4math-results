import Research.TaskH.Six.TraceSixPathMoments
import Research.TaskH.Six.TraceSixCommonIdentity

/-!
The exact actual six-cycle trace and Frobenius identities.  Every path,
overlap, common-neighbor and matrix term is supplied by the original graph
modules; neither identity is assumed as a premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_defect_row_square_sum (a : V) :
    (∑ v : V, (traceDefect G a v) ^ 2) =
      (∑ v : V, (traceAdjacencyPower G 3 a v) ^ 2) -
        6 * ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a +
          9 * ((G.degree a : ℝ) - 1) ^ 2 * (G.degree a : ℝ) := by
  calc
    _ = ∑ v : V, ((traceAdjacencyPower G 3 a v) ^ 2 -
        (6 * ((G.degree a : ℝ) - 1)) *
          (G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) +
            (9 * ((G.degree a : ℝ) - 1) ^ 2) * G.adjMatrix ℝ a v) := by
      apply Finset.sum_congr rfl
      intro v _
      change (traceAdjacencyPower G 3 a v -
        3 * ((G.degree a : ℝ) - 1) * G.adjMatrix ℝ a v) ^ 2 = _
      calc
        _ = (traceAdjacencyPower G 3 a v) ^ 2 -
            (6 * ((G.degree a : ℝ) - 1)) *
              (G.adjMatrix ℝ a v * traceAdjacencyPower G 3 a v) +
                (9 * ((G.degree a : ℝ) - 1) ^ 2) * (G.adjMatrix ℝ a v) ^ 2 := by
          ring
        _ = _ := by rw [trace_adjacency_entry_sq]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [trace_cube_dot_row, trace_adjacency_row_sum]

theorem trace_defect_square_moment_identity :
    traceDefectSquare G =
      (∑ a : V, traceAdjacencyPower G 6 a a) -
        6 * (∑ a : V, ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
          9 * traceDegreeMoment G 3 - 18 * traceDegreeMoment G 2 +
            9 * traceDegreeMoment G 1 := by
  have hd : (∑ a : V, ((G.degree a : ℝ) - 1) ^ 2 * (G.degree a : ℝ)) =
      traceDegreeMoment G 3 - 2 * traceDegreeMoment G 2 + traceDegreeMoment G 1 := by
    calc
      _ = ∑ a : V, ((G.degree a : ℝ) ^ 3 - 2 * (G.degree a : ℝ) ^ 2 + (G.degree a : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          traceDegreeMoment, pow_one]
  calc
    _ = ∑ a : V, ((∑ v : V, (traceAdjacencyPower G 3 a v) ^ 2) -
        6 * ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a +
          9 * ((G.degree a : ℝ) - 1) ^ 2 * (G.degree a : ℝ)) :=
      Finset.sum_congr rfl (fun a _ => trace_defect_row_square_sum a)
    _ = (∑ a : V, ∑ v : V, (traceAdjacencyPower G 3 a v) ^ 2) -
        6 * (∑ a : V, ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
          9 * (∑ a : V, ((G.degree a : ℝ) - 1) ^ 2 * (G.degree a : ℝ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    _ = _ := by
      rw [trace_sixth_diagonal_sum, hd]
      ring

theorem trace_actual_six_cycle_trace_identity :
    12 * ((actualSixEdgeSets G).card : ℝ) =
      (∑ a : V, traceAdjacencyPower G 6 a a) -
        6 * (∑ a : V, ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) -
          12 * traceTriangleMoment G 2 + 10 * traceTriangleMoment G 1 +
            18 * traceOrientedDiamondPairs G + 4 * traceDegreeMoment G 3 -
              12 * traceDegreeMoment G 2 + 4 * traceDegreeMoment G 1 +
                3 * traceOrderedDegreeProduct G := by
  have hc := trace_actual_six_cycle_common_count_identity (G := G)
  have hp := trace_simple_path_pair_moment_formula (G := G)
  have hL := trace_weighted_common_choose_moment_formula (G := G)
  have hW :
      2 * (∑ a : V, (2 * (G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) +
        2 * (∑ a : V, ((G.degree a : ℝ) - 2) * traceAdjacencyPower G 4 a a) =
          6 * (∑ a : V, ((G.degree a : ℝ) - 1) * traceAdjacencyPower G 4 a a) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  linarith

theorem trace_actual_six_cycle_frobenius_identity :
    12 * ((actualSixEdgeSets G).card : ℝ) =
      traceDefectSquare G - 5 * traceDegreeMoment G 3 + 6 * traceDegreeMoment G 2 -
        5 * traceDegreeMoment G 1 + 3 * traceOrderedDegreeProduct G -
          12 * traceTriangleMoment G 2 + 10 * traceTriangleMoment G 1 +
            18 * traceOrientedDiamondPairs G := by
  have hc := trace_actual_six_cycle_trace_identity (G := G)
  have hm := trace_defect_square_moment_identity (G := G)
  linarith

end TaskH.Six

#print axioms TaskH.Six.trace_defect_row_square_sum
#print axioms TaskH.Six.trace_defect_square_moment_identity
#print axioms TaskH.Six.trace_actual_six_cycle_trace_identity
#print axioms TaskH.Six.trace_actual_six_cycle_frobenius_identity
