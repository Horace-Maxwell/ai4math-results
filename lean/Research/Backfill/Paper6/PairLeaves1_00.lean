import Research.Backfill.Paper6.PairCounts

/-! Numerical obligations only: generated, not executed. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

-- Static assignment upper bound: 64.
set_option maxHeartbeats 200000 in
theorem pair_leaf1_root : pairSuffix1Depth0  = true := by
  decide +kernel

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.pair_leaf1_root
