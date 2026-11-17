import Research.TaskH.Six.TraceSixBacktrackSets
import Research.TaskH.Six.TraceSixFrobenius

/-!
Actual three-step adjacency-matrix entries and exact backtrack removal.
The simple-path formula is stated only for different endpoints; diagonal
entries count triangles and are not silently treated as simple paths.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_adjacency_cube_entry (u v : V) :
    traceAdjacencyPower G 3 u v =
      ∑ a : V, ∑ b : V,
        G.adjMatrix ℝ u a * G.adjMatrix ℝ a b * G.adjMatrix ℝ b v := by
  classical
  change (G.adjMatrix ℝ ^ 3) u v = _
  have hp : G.adjMatrix ℝ ^ 3 = (G.adjMatrix ℝ * G.adjMatrix ℝ) * G.adjMatrix ℝ := by
    simp [pow_succ]
  rw [hp, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem traceThreeWalkPairs_card_eq_adjacency_cube (u v : V) :
    ((traceThreeWalkPairs G u v).card : ℝ) = traceAdjacencyPower G 3 u v := by
  classical
  have hn : (traceThreeWalkPairs G u v).card =
      ∑ p : V × V, if IsTraceThreeWalk G u v p then 1 else 0 := by
    rw [traceThreeWalkPairs, Finset.card_filter]
  have hr : ((traceThreeWalkPairs G u v).card : ℝ) =
      ∑ p : V × V, if IsTraceThreeWalk G u v p then (1 : ℝ) else 0 := by
    exact_mod_cast hn
  rw [hr, Fintype.sum_prod_type, trace_adjacency_cube_entry]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hua : G.Adj u a <;> by_cases hab : G.Adj a b <;>
    by_cases hbv : G.Adj b v <;>
      simp [IsTraceThreeWalk, SimpleGraph.adjMatrix_apply, hua, hab, hbv]

theorem traceThreeWalkPairs_card_backtrack_balance (u v : V) (huv : u ≠ v) :
    (traceThreeWalkPairs G u v).card + (if G.Adj u v then 1 else 0) =
      (traceThreePaths G u v).card +
        (if G.Adj u v then G.degree v else 0) +
          (if G.Adj u v then G.degree u else 0) := by
  have h := traceThreeWalkPairs_card_inclusion_exclusion (G := G) u v huv
  rw [traceBacktracks_inter_card, traceEarlyBacktracks_card,
    traceLateBacktracks_card] at h
  exact h

theorem traceThreePaths_card_eq_adjacency_cube_corrected (u v : V) (huv : u ≠ v) :
    ((traceThreePaths G u v).card : ℝ) =
      traceAdjacencyPower G 3 u v -
        ((G.degree u : ℝ) + (G.degree v : ℝ) - 1) * G.adjMatrix ℝ u v := by
  classical
  have hb := traceThreeWalkPairs_card_backtrack_balance (G := G) u v huv
  have hw := traceThreeWalkPairs_card_eq_adjacency_cube (G := G) u v
  by_cases he : G.Adj u v
  · simp only [ite_eq_left he] at hb
    have hr : ((traceThreeWalkPairs G u v).card : ℝ) + 1 =
        (traceThreePaths G u v).card + (G.degree v : ℝ) + (G.degree u : ℝ) := by
      exact_mod_cast hb
    rw [← hw]
    simp only [SimpleGraph.adjMatrix_apply, ite_eq_left he, mul_one]
    linarith
  · have heq : (traceThreeWalkPairs G u v).card = (traceThreePaths G u v).card := by
      simpa only [ite_eq_right he, Nat.add_zero] using hb
    rw [← hw, heq]
    simp only [SimpleGraph.adjMatrix_apply, ite_eq_right he, mul_zero, sub_zero]

end TaskH.Six

#print axioms TaskH.Six.trace_adjacency_cube_entry
#print axioms TaskH.Six.traceThreeWalkPairs_card_eq_adjacency_cube
#print axioms TaskH.Six.traceThreeWalkPairs_card_backtrack_balance
#print axioms TaskH.Six.traceThreePaths_card_eq_adjacency_cube_corrected
