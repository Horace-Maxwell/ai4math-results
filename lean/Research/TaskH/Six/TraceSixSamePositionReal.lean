import Research.TaskH.Six.TraceSixNeighborCounts
import Research.TaskH.Six.TraceSixSamePosition
import Research.TaskH.Six.TraceSixFrobenius

/-!
Transport the actual natural same-position budget to its real polynomial.
The subtraction is justified internally whenever a common-neighbor pair
exists; when no pair exists its binomial coefficient is exactly zero.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_common_degree_budget (a v : V) :
    (traceCommonNeighbors G a v).card + (if G.Adj a v then 1 else 0) ≤ G.degree a := by
  classical
  by_cases hav : G.Adj a v
  · have hs : insert v (traceCommonNeighbors G a v) ⊆ G.neighborFinset a := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxv | hc
      · subst x
        exact (G.mem_neighborFinset a v).mpr hav
      · exact (G.mem_neighborFinset a x).mpr
          ((mem_traceCommonNeighbors_iff a v x).mp hc).1
    have hh := Finset.card_le_card hs
    rw [Finset.card_insert_of_notMem (traceCommonNeighbors_not_right a v),
      G.card_neighborFinset_eq_degree a] at hh
    simpa only [ite_eq_left hav] using hh
  · have hs : traceCommonNeighbors G a v ⊆ G.neighborFinset a := by
      intro x hx
      exact (G.mem_neighborFinset a x).mpr
        ((mem_traceCommonNeighbors_iff a v x).mp hx).1
    have hh := Finset.card_le_card hs
    rw [G.card_neighborFinset_eq_degree a] at hh
    simpa only [ite_eq_right hav, Nat.add_zero] using hh

theorem trace_same_position_coefficient_cast (a v : V)
    (hc : 2 ≤ (traceCommonNeighbors G a v).card) :
    ((G.degree a - 2 - (if G.Adj a v then 1 else 0) : ℕ) : ℝ) =
      (G.degree a : ℝ) - 2 - G.adjMatrix ℝ a v := by
  have hb := trace_common_degree_budget (G := G) a v
  have hd2 : 2 ≤ G.degree a := by omega
  have hdi : (if G.Adj a v then 1 else 0) ≤ G.degree a - 2 := by omega
  have hcast : ((G.degree a - 2 - (if G.Adj a v then 1 else 0) : ℕ) : ℝ) =
      (G.degree a : ℝ) - 2 - ((if G.Adj a v then 1 else 0 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdi, Nat.cast_sub hd2]
    norm_num
  have hi : ((if G.Adj a v then 1 else 0 : ℕ) : ℝ) = G.adjMatrix ℝ a v := by
    by_cases hav : G.Adj a v
    · simp only [ite_eq_left hav, SimpleGraph.adjMatrix_apply, Nat.cast_one]
    · simp only [ite_eq_right hav, SimpleGraph.adjMatrix_apply, Nat.cast_zero]
  rw [hcast, hi]

open scoped Classical in
theorem trace_same_position_row_cast (a v : V) :
    ((if a ≠ v then
      (G.degree a - 2 - (if G.Adj a v then 1 else 0)) *
        (traceCommonNeighbors G a v).card.choose 2 else 0 : ℕ) : ℝ) =
      if a ≠ v then ((G.degree a : ℝ) - 2 - G.adjMatrix ℝ a v) *
        ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0 := by
  classical
  by_cases hav : a ≠ v
  · rw [ite_eq_left hav, ite_eq_left hav]
    by_cases hc : 2 ≤ (traceCommonNeighbors G a v).card
    · rw [Nat.cast_mul, trace_same_position_coefficient_cast a v hc]
    · have hz : (traceCommonNeighbors G a v).card.choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz, Nat.cast_zero, mul_zero]
  · simp only [ite_eq_right hav, Nat.cast_zero]

noncomputable def traceSamePositionRealBudget (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ := by
  classical
  exact ∑ a : V, ∑ v : V, if a ≠ v then
    ((G.degree a : ℝ) - 2 - G.adjMatrix ℝ a v) *
      ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0

noncomputable def traceWeightedCommonChoose (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℝ := by
  classical
  exact ∑ a : V, ∑ v : V, if a ≠ v then
    ((G.degree a : ℝ) - 2) * ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0

theorem trace_same_position_budget_cast :
    (traceSamePositionBudget G : ℝ) = traceSamePositionRealBudget G := by
  classical
  unfold traceSamePositionBudget traceSamePositionRealBudget
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun v _ => trace_same_position_row_cast a v)

theorem trace_same_position_total_card_real :
    ((traceOverlapWords G 1).card : ℝ) + (traceOverlapWords G 2).card =
      4 * traceSamePositionRealBudget G := by
  have hn := trace_same_position_total_card (G := G)
  have hr : ((traceOverlapWords G 1).card : ℝ) + (traceOverlapWords G 2).card =
      4 * (traceSamePositionBudget G : ℝ) := by
    exact_mod_cast hn
  rw [trace_same_position_budget_cast] at hr
  exact hr

open scoped Classical in
theorem trace_adjacent_common_choose_sum :
    (∑ a : V, ∑ v : V, if a ≠ v then
      G.adjMatrix ℝ a v * ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0) =
      (traceOrientedDiamondPairs G : ℝ) := by
  classical
  calc
    _ = ∑ a : V, ∑ v : V,
        G.adjMatrix ℝ a v * ((traceCommonNeighbors G a v).card.choose 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro v _
      by_cases hav : a ≠ v
      · rw [ite_eq_left hav]
      · have he : a = v := not_ne_iff.mp hav
        subst v
        simp
    _ = ∑ a : V, ∑ v ∈ G.neighborFinset a,
        ((traceCommonNeighbors G a v).card.choose 2 : ℝ) :=
      Finset.sum_congr rfl (fun a _ => trace_adjacency_weighted_row_sum a
        (fun v => ((traceCommonNeighbors G a v).card.choose 2 : ℝ)))
    _ = _ := by simp only [traceOrientedDiamondPairs, Nat.cast_sum]

theorem trace_same_position_real_budget_eq_weighted_sub_diamond :
    traceSamePositionRealBudget G =
      traceWeightedCommonChoose G - traceOrientedDiamondPairs G := by
  classical
  calc
    _ = (∑ a : V, ∑ v : V, if a ≠ v then
        ((G.degree a : ℝ) - 2) * ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0) -
        ∑ a : V, ∑ v : V, if a ≠ v then
          G.adjMatrix ℝ a v * ((traceCommonNeighbors G a v).card.choose 2 : ℝ) else 0 := by
      unfold traceSamePositionRealBudget
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hav : a ≠ v
      · simp only [ite_eq_left hav]
        ring
      · simp only [ite_eq_right hav, sub_zero]
    _ = _ := by
      rw [trace_adjacent_common_choose_sum]
      rfl

end TaskH.Six

#print axioms TaskH.Six.trace_common_degree_budget
#print axioms TaskH.Six.trace_same_position_coefficient_cast
#print axioms TaskH.Six.trace_same_position_row_cast
#print axioms TaskH.Six.trace_same_position_budget_cast
#print axioms TaskH.Six.trace_same_position_total_card_real
#print axioms TaskH.Six.trace_adjacent_common_choose_sum
#print axioms TaskH.Six.trace_same_position_real_budget_eq_weighted_sub_diamond
