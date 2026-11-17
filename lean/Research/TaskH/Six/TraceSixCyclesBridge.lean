import Research.TaskH.Six.TraceSixDoubleCross
import Research.TaskH.Six.HexagonWordsCardinality

/-!
The path-pair classification counts the original undirected six-cycle edge
sets via the actual twelve-to-one hexagon map.  There is no ShortSixCycles
premise: actual length-six edge sets are used throughout this identity.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

theorem trace_cast_pair_polynomial (n : ℕ) :
    ((n ^ 2 - n : ℕ) : ℝ) = (n : ℝ) ^ 2 - n := by
  have hn : n ≤ n ^ 2 := by
    cases n with
    | zero => simp
    | succ n => nlinarith
  rw [Nat.cast_sub hn, Nat.cast_pow]

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem traceOverlapWords_zero_eq_hexagonWords :
    traceOverlapWords G 0 = hexagonWords G := by
  rw [traceOverlapWords_zero]
  rfl

theorem traceOverlapWords_zero_card :
    (traceOverlapWords G 0).card = 12 * (actualSixEdgeSets G).card := by
  rw [traceOverlapWords_zero_eq_hexagonWords,
    hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card]

variable [DecidableRel G.Adj]

theorem trace_actual_six_pair_count_identity :
    12 * (actualSixEdgeSets G).card +
        (traceOverlapWords G 1).card + (traceOverlapWords G 2).card +
          (traceOverlapWords G 3).card + (traceOverlapWords G 4).card +
            2 * traceOrientedDiamondPairs G =
      ∑ u : V, ∑ v : V,
        ((traceThreePaths G u v).card ^ 2 - (traceThreePaths G u v).card) := by
  have hc := trace_three_path_pair_count_identity (G := G)
  change (hexagonWords G).card +
      (traceOverlapWords G 1).card + (traceOverlapWords G 2).card +
        (traceOverlapWords G 3).card + (traceOverlapWords G 4).card +
          (traceOverlapWords G 5).card = _ at hc
  rw [hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card,
    trace_double_cross_card] at hc
  exact hc

theorem trace_actual_six_pair_count_identity_real :
    12 * ((actualSixEdgeSets G).card : ℝ) +
        (traceOverlapWords G 1).card + (traceOverlapWords G 2).card +
          (traceOverlapWords G 3).card + (traceOverlapWords G 4).card +
            2 * traceOrientedDiamondPairs G =
      ∑ u : V, ∑ v : V,
        (((traceThreePaths G u v).card : ℝ) ^ 2 - (traceThreePaths G u v).card) := by
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (trace_actual_six_pair_count_identity (G := G))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
    trace_cast_pair_polynomial] using hc

end TaskH.Six

#print axioms TaskH.Six.trace_cast_pair_polynomial
#print axioms TaskH.Six.traceOverlapWords_zero_eq_hexagonWords
#print axioms TaskH.Six.traceOverlapWords_zero_card
#print axioms TaskH.Six.trace_actual_six_pair_count_identity
#print axioms TaskH.Six.trace_actual_six_pair_count_identity_real
