import Research.Backfill.Paper6.PairLeaves3_71

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

set_option maxHeartbeats 400000 in
theorem assembled_pair3_6 : pairSuffix3Depth1 6 = true := by
  unfold pairSuffix3Depth1
  apply allLe_intro
  intro b7 hb7
  norm_num at hb7
  have hb7_cases_upper : b7 ≤ 1 := by omega
  interval_cases b7
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 1 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_6_0_0_0
      · exact pair_leaf3_6_0_0_1
    · exact pair_leaf3_6_0_1
  · exact pair_leaf3_6_1

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.assembled_pair3_6
