import Research.Backfill.Paper6.PairCounts

/-! Numerical obligations only: generated, not executed. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

-- Static assignment upper bound: 2772.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_0_1_1 : pairSuffix3Depth4 5 0 1 1 = true := by
  decide +kernel

-- Static assignment upper bound: 1716.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_0_2 : pairSuffix3Depth3 5 0 2 = true := by
  decide +kernel

-- Static assignment upper bound: 9702.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_1_0_0 : pairSuffix3Depth4 5 1 0 0 = true := by
  decide +kernel

-- Static assignment upper bound: 5292.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_1_0_1 : pairSuffix3Depth4 5 1 0 1 = true := by
  decide +kernel

-- Static assignment upper bound: 5544.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_1_1 : pairSuffix3Depth3 5 1 1 = true := by
  decide +kernel

-- Static assignment upper bound: 9702.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_5_2_0 : pairSuffix3Depth3 5 2 0 = true := by
  decide +kernel

-- Static assignment upper bound: 4752.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_6_0_0_0 : pairSuffix3Depth4 6 0 0 0 = true := by
  decide +kernel

-- Static assignment upper bound: 2772.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_6_0_0_1 : pairSuffix3Depth4 6 0 0 1 = true := by
  decide +kernel

-- Static assignment upper bound: 1716.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_6_0_1 : pairSuffix3Depth3 6 0 1 = true := by
  decide +kernel

-- Static assignment upper bound: 6468.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_6_1 : pairSuffix3Depth2 6 1 = true := by
  decide +kernel

-- Static assignment upper bound: 3432.
set_option maxHeartbeats 200000 in
theorem pair_leaf3_7 : pairSuffix3Depth1 7 = true := by
  decide +kernel

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.pair_leaf3_5_0_1_1
#print axioms Paper6FiveExclusion.pair_leaf3_5_0_2
#print axioms Paper6FiveExclusion.pair_leaf3_5_1_0_0
#print axioms Paper6FiveExclusion.pair_leaf3_5_1_0_1
#print axioms Paper6FiveExclusion.pair_leaf3_5_1_1
#print axioms Paper6FiveExclusion.pair_leaf3_5_2_0
#print axioms Paper6FiveExclusion.pair_leaf3_6_0_0_0
#print axioms Paper6FiveExclusion.pair_leaf3_6_0_0_1
#print axioms Paper6FiveExclusion.pair_leaf3_6_0_1
#print axioms Paper6FiveExclusion.pair_leaf3_6_1
#print axioms Paper6FiveExclusion.pair_leaf3_7
