import Research.Backfill.Paper6.PairLeaves3_71

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

set_option maxHeartbeats 400000 in
theorem assembled_pair3_7 : pairSuffix3Depth1 7 = true := by
  exact pair_leaf3_7

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.assembled_pair3_7
