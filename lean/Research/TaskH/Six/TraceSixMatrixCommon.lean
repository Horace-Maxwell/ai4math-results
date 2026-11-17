import Research.TaskH.Six.TraceSixSamePositionReal
import Research.TaskH.Six.TraceSixBacktracks

/-!
Actual adjacency powers and common-neighbor sums.  Diagonal terms are
retained explicitly: common(a,a)=degree(a), and A^3(a,a)=2*t_a.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

theorem trace_choose_two_real (n : ℕ) :
    (n.choose 2 : ℝ) = ((n : ℝ) ^ 2 - n) / 2 := by
  rw [Nat.cast_choose_two]
  ring

variable {V : Type u} [Fintype V]

open scoped Classical in
theorem trace_offdiagonal_sum (F : V → ℝ) (a : V) :
    (∑ v : V, if a ≠ v then F v else 0) = (∑ v : V, F v) - F a := by
  classical
  have hs := Finset.sum_erase_add (Finset.univ : Finset V) F (Finset.mem_univ a)
  have he : (Finset.univ : Finset V).erase a = Finset.univ.filter (fun v => a ≠ v) := by
    ext v
    simp [ne_comm]
  rw [he, Finset.sum_filter] at hs
  linarith

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_adjacency_power_symm (r : ℕ) (a v : V) :
    traceAdjacencyPower G r a v = traceAdjacencyPower G r v a := by
  classical
  exact ((G.isSymm_adjMatrix (α := ℝ)).pow r).apply v a

theorem trace_adjacency_square_entry (a v : V) :
    traceAdjacencyPower G 2 a v = ((traceCommonNeighbors G a v).card : ℝ) := by
  classical
  have he : traceCommonNeighbors G a v =
      Finset.univ.filter (fun x => G.Adj a x ∧ G.Adj v x) := by
    ext x
    simp only [mem_traceCommonNeighbors_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  have hn : (traceCommonNeighbors G a v).card =
      ∑ x : V, if G.Adj a x ∧ G.Adj v x then 1 else 0 := by
    rw [he, Finset.card_filter]
  have hr : ((traceCommonNeighbors G a v).card : ℝ) =
      ∑ x : V, if G.Adj a x ∧ G.Adj v x then (1 : ℝ) else 0 := by
    exact_mod_cast hn
  rw [hr]
  change (G.adjMatrix ℝ ^ 2) a v = _
  rw [pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hax : G.Adj a x <;> by_cases hvx : G.Adj v x <;>
    simp_all [SimpleGraph.adjMatrix_apply, G.adj_comm]

theorem trace_common_diagonal_card (a : V) :
    (traceCommonNeighbors G a a).card = G.degree a := by
  classical
  have he : traceCommonNeighbors G a a = G.neighborFinset a := by
    ext x
    simp only [mem_traceCommonNeighbors_iff, SimpleGraph.mem_neighborFinset, and_self]
  rw [he, G.card_neighborFinset_eq_degree a]

theorem trace_even_power_diagonal (r : ℕ) (a : V) :
    traceAdjacencyPower G (2 * r) a a =
      ∑ v : V, (traceAdjacencyPower G r a v) ^ 2 := by
  classical
  change (G.adjMatrix ℝ ^ (2 * r)) a a = ∑ v : V, ((G.adjMatrix ℝ ^ r) a v) ^ 2
  rw [two_mul, pow_add, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro v _
  change traceAdjacencyPower G r a v * traceAdjacencyPower G r v a =
    (traceAdjacencyPower G r a v) ^ 2
  rw [trace_adjacency_power_symm r v a, pow_two]

theorem trace_fourth_diagonal_common_square (a : V) :
    traceAdjacencyPower G 4 a a =
      ∑ v : V, ((traceCommonNeighbors G a v).card : ℝ) ^ 2 := by
  calc
    _ = ∑ v : V, (traceAdjacencyPower G 2 a v) ^ 2 := trace_even_power_diagonal 2 a
    _ = _ := Finset.sum_congr rfl (fun v _ => by rw [trace_adjacency_square_entry])

theorem trace_sixth_diagonal_sum :
    (∑ a : V, ∑ v : V, (traceAdjacencyPower G 3 a v) ^ 2) =
      ∑ a : V, traceAdjacencyPower G 6 a a := by
  exact Finset.sum_congr rfl (fun a _ => (trace_even_power_diagonal 3 a).symm)

theorem trace_cube_diagonal_triangle (a : V) :
    traceAdjacencyPower G 3 a a = 2 * (traceLocalTriangleCount G a : ℝ) := by
  classical
  have hp : G.adjMatrix ℝ ^ 3 = G.adjMatrix ℝ * (G.adjMatrix ℝ ^ 2) := by
    rw [pow_succ']
  change (G.adjMatrix ℝ ^ 3) a a = _
  rw [hp, G.adjMatrix_mul_apply]
  change (∑ x ∈ G.neighborFinset a, traceAdjacencyPower G 2 x a) = _
  calc
    _ = ∑ x ∈ G.neighborFinset a, ((traceCommonNeighbors G a x).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [trace_adjacency_power_symm 2 x a, trace_adjacency_square_entry]
    _ = _ := by exact_mod_cast (trace_common_neighbor_linear_sum (G := G) a)

theorem trace_common_row_sum_real (a : V) :
    (∑ v : V, ((traceCommonNeighbors G a v).card : ℝ)) =
      ∑ x ∈ G.neighborFinset a, (G.degree x : ℝ) := by
  classical
  calc
    _ = ∑ v : V, traceAdjacencyPower G 2 a v :=
      Finset.sum_congr rfl (fun v _ => (trace_adjacency_square_entry a v).symm)
    _ = ∑ x : V, G.adjMatrix ℝ a x * ∑ v : V, G.adjMatrix ℝ x v := by
      change (∑ v : V, (G.adjMatrix ℝ ^ 2) a v) = _
      rw [pow_two]
      exact trace_matrix_row_product_sum (G.adjMatrix ℝ) (G.adjMatrix ℝ) a
    _ = ∑ x : V, G.adjMatrix ℝ a x * (G.degree x : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [trace_adjacency_row_sum]
    _ = _ := trace_adjacency_weighted_row_sum a (fun x => (G.degree x : ℝ))

open scoped Classical in
theorem trace_common_offdiag_linear_sum (a : V) :
    (∑ v : V, if a ≠ v then ((traceCommonNeighbors G a v).card : ℝ) else 0) =
      (∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) - G.degree a := by
  rw [trace_offdiagonal_sum, trace_common_row_sum_real, trace_common_diagonal_card]

open scoped Classical in
theorem trace_common_offdiag_square_sum (a : V) :
    (∑ v : V, if a ≠ v then ((traceCommonNeighbors G a v).card : ℝ) ^ 2 else 0) =
      traceAdjacencyPower G 4 a a - (G.degree a : ℝ) ^ 2 := by
  rw [trace_offdiagonal_sum, ← trace_fourth_diagonal_common_square,
    trace_common_diagonal_card]

open scoped Classical in
theorem trace_weighted_common_choose_row (a : V) :
    (∑ v : V, if a ≠ v then ((G.degree a : ℝ) - 2) *
      ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0) =
      ((G.degree a : ℝ) - 2) / 2 *
        (traceAdjacencyPower G 4 a a - (G.degree a : ℝ) ^ 2 -
          (∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) + G.degree a) := by
  classical
  calc
    _ = ((G.degree a : ℝ) - 2) / 2 *
        ((∑ v : V, if a ≠ v then ((traceCommonNeighbors G a v).card : ℝ) ^ 2 else 0) -
          ∑ v : V, if a ≠ v then ((traceCommonNeighbors G a v).card : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hav : a ≠ v
      · simp only [ite_eq_left hav, trace_choose_two_real]
        ring
      · simp only [ite_eq_right hav, sub_zero, mul_zero]
    _ = _ := by
      rw [trace_common_offdiag_square_sum, trace_common_offdiag_linear_sum]
      ring

theorem trace_weighted_common_choose_matrix_formula :
    traceWeightedCommonChoose G =
      ∑ a : V, ((G.degree a : ℝ) - 2) / 2 *
        (traceAdjacencyPower G 4 a a - (G.degree a : ℝ) ^ 2 -
          (∑ x ∈ G.neighborFinset a, (G.degree x : ℝ)) + G.degree a) := by
  classical
  unfold traceWeightedCommonChoose
  exact Finset.sum_congr rfl (fun a _ => trace_weighted_common_choose_row a)

end TaskH.Six

#print axioms TaskH.Six.trace_choose_two_real
#print axioms TaskH.Six.trace_offdiagonal_sum
#print axioms TaskH.Six.trace_adjacency_power_symm
#print axioms TaskH.Six.trace_adjacency_square_entry
#print axioms TaskH.Six.trace_common_diagonal_card
#print axioms TaskH.Six.trace_even_power_diagonal
#print axioms TaskH.Six.trace_fourth_diagonal_common_square
#print axioms TaskH.Six.trace_sixth_diagonal_sum
#print axioms TaskH.Six.trace_cube_diagonal_triangle
#print axioms TaskH.Six.trace_common_row_sum_real
#print axioms TaskH.Six.trace_common_offdiag_linear_sum
#print axioms TaskH.Six.trace_common_offdiag_square_sum
#print axioms TaskH.Six.trace_weighted_common_choose_row
#print axioms TaskH.Six.trace_weighted_common_choose_matrix_formula
