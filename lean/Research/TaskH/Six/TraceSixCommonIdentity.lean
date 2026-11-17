import Research.TaskH.Six.TraceSixSamePositionReal
import Research.TaskH.Six.TraceSixCyclesBridge

/-!
All overlap terms of the actual simple-threepath pair count have now been
evaluated.  This is the exact actual six-cycle/common-neighbor identity;
conversion of the remaining path and weighted-common sums into matrix
traces is a further algebraic transport, not a new premise here.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem trace_actual_six_cycle_common_count_identity :
    12 * ((actualSixEdgeSets G).card : ℝ) =
      (∑ u : V, ∑ v : V,
        (((traceThreePaths G u v).card : ℝ) ^ 2 - (traceThreePaths G u v).card)) -
        4 * traceWeightedCommonChoose G - 8 * traceTriangleMoment G 2 +
          8 * traceTriangleMoment G 1 + 18 * traceOrientedDiamondPairs G := by
  have hp := trace_actual_six_pair_count_identity_real (G := G)
  have hs := trace_same_position_total_card_real (G := G)
  have hb := trace_same_position_real_budget_eq_weighted_sub_diamond (G := G)
  have hc := trace_single_cross_total_card_canonical (G := G)
  linarith

end TaskH.Six

#print axioms TaskH.Six.trace_actual_six_cycle_common_count_identity
