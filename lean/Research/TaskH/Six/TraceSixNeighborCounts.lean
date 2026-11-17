import Research.TaskH.Six.TraceSixSingleCross
import Research.TaskH.Six.TraceSixDoubleCross

/-!
Canonical actual common-neighbor sums.  The linear count is the actual
degree-sum formula in each induced neighborhood graph; the quadratic
count uses the exact finite two-element-subset polynomial.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

theorem trace_nat_square_eq_two_choose_add (n : ℕ) :
    n ^ 2 = 2 * n.choose 2 + n := by
  have he : n * n - n = 2 * n.choose 2 := by
    simpa only [Finset.offDiag_card, Finset.card_range] using
      trace_offDiag_card_eq_two_choose (Finset.range n)
  have hn : n ≤ n * n := by
    cases n with
    | zero => simp
    | succ n => nlinarith
  rw [pow_two]
  omega

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_common_neighbor_linear_sum (a : V) :
    (∑ x ∈ G.neighborFinset a, (traceCommonNeighbors G a x).card) =
      2 * traceLocalTriangleCount G a := by
  classical
  calc
    _ = ∑ x : G.neighborSet a, (traceCommonNeighbors G a (x : V)).card :=
      Finset.sum_subtype (G.neighborFinset a) (fun x => G.mem_neighborFinset a x)
        (fun x => (traceCommonNeighbors G a x).card)
    _ = ∑ x : G.neighborSet a, (G.induce (G.neighborSet a)).degree x :=
      Finset.sum_congr rfl (fun x _ => (trace_neighbor_degree_eq_common_card a x).symm)
    _ = 2 * (G.induce (G.neighborSet a)).edgeFinset.card :=
      (G.induce (G.neighborSet a)).sum_degrees_eq_twice_card_edges
    _ = _ := rfl

theorem trace_common_global_linear_sum :
    (∑ a : V, ∑ x ∈ G.neighborFinset a, (traceCommonNeighbors G a x).card) =
      2 * ∑ a : V, traceLocalTriangleCount G a := by
  calc
    _ = ∑ a : V, 2 * traceLocalTriangleCount G a :=
      Finset.sum_congr rfl (fun a _ => trace_common_neighbor_linear_sum a)
    _ = _ := by rw [Finset.mul_sum]

theorem trace_common_global_square_sum :
    (∑ a : V, ∑ x ∈ G.neighborFinset a, (traceCommonNeighbors G a x).card ^ 2) =
      2 * traceOrientedDiamondPairs G + 2 * ∑ a : V, traceLocalTriangleCount G a := by
  calc
    _ = ∑ a : V, ∑ x ∈ G.neighborFinset a,
        (2 * (traceCommonNeighbors G a x).card.choose 2 +
          (traceCommonNeighbors G a x).card) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_congr rfl (fun x _ =>
        trace_nat_square_eq_two_choose_add (traceCommonNeighbors G a x).card)
    _ = 2 * traceOrientedDiamondPairs G +
        ∑ a : V, ∑ x ∈ G.neighborFinset a, (traceCommonNeighbors G a x).card := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, traceOrientedDiamondPairs]
    _ = _ := by rw [trace_common_global_linear_sum]

theorem trace_common_global_linear_sum_real :
    (∑ a : V, ∑ x ∈ G.neighborFinset a, ((traceCommonNeighbors G a x).card : ℝ)) =
      2 * traceTriangleMoment G 1 := by
  have hn := trace_common_global_linear_sum (G := G)
  have hr : (∑ a : V, ∑ x ∈ G.neighborFinset a,
      ((traceCommonNeighbors G a x).card : ℝ)) =
      2 * ∑ a : V, (traceLocalTriangleCount G a : ℝ) := by
    exact_mod_cast hn
  simpa only [traceTriangleMoment, pow_one] using hr

theorem trace_common_global_square_sum_real :
    (∑ a : V, ∑ x ∈ G.neighborFinset a, ((traceCommonNeighbors G a x).card : ℝ) ^ 2) =
      2 * traceOrientedDiamondPairs G + 2 * traceTriangleMoment G 1 := by
  have hn := trace_common_global_square_sum (G := G)
  have hr : (∑ a : V, ∑ x ∈ G.neighborFinset a,
      ((traceCommonNeighbors G a x).card : ℝ) ^ 2) =
      2 * traceOrientedDiamondPairs G +
        2 * ∑ a : V, (traceLocalTriangleCount G a : ℝ) := by
    exact_mod_cast hn
  simpa only [traceTriangleMoment, pow_one] using hr

theorem trace_single_cross_total_card_canonical :
    ((traceOverlapWords G 3).card : ℝ) + (traceOverlapWords G 4).card =
      8 * traceTriangleMoment G 2 - 8 * traceTriangleMoment G 1 -
        16 * traceOrientedDiamondPairs G := by
  have hc := trace_single_cross_total_card_real (G := G)
  rw [trace_common_global_square_sum_real] at hc
  linarith

end TaskH.Six

#print axioms TaskH.Six.trace_nat_square_eq_two_choose_add
#print axioms TaskH.Six.trace_common_neighbor_linear_sum
#print axioms TaskH.Six.trace_common_global_linear_sum
#print axioms TaskH.Six.trace_common_global_square_sum
#print axioms TaskH.Six.trace_common_global_linear_sum_real
#print axioms TaskH.Six.trace_common_global_square_sum_real
#print axioms TaskH.Six.trace_single_cross_total_card_canonical
