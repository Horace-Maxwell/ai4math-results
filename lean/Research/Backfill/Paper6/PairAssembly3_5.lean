import Research.Backfill.Paper6.PairLeaves3_70
import Research.Backfill.Paper6.PairLeaves3_71

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

set_option maxHeartbeats 400000 in
theorem assembled_pair3_5 : pairSuffix3Depth1 5 = true := by
  unfold pairSuffix3Depth1
  apply allLe_intro
  intro b7 hb7
  norm_num at hb7
  have hb7_cases_upper : b7 ≤ 2 := by omega
  interval_cases b7
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 2 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 2 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_5_0_0_0_0_0
          · exact pair_leaf3_5_0_0_0_0_1
          · exact pair_leaf3_5_0_0_0_0_2
        · exact pair_leaf3_5_0_0_0_1
        · exact pair_leaf3_5_0_0_0_2
      · exact pair_leaf3_5_0_0_1
      · exact pair_leaf3_5_0_0_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_5_0_1_0
      · exact pair_leaf3_5_0_1_1
    · exact pair_leaf3_5_0_2
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
      · exact pair_leaf3_5_1_0_0
      · exact pair_leaf3_5_1_0_1
    · exact pair_leaf3_5_1_1
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 0 := by omega
    interval_cases a6
    · exact pair_leaf3_5_2_0

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.assembled_pair3_5
