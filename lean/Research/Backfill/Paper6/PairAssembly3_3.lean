import Research.Backfill.Paper6.PairLeaves3_66
import Research.Backfill.Paper6.PairLeaves3_67
import Research.Backfill.Paper6.PairLeaves3_68
import Research.Backfill.Paper6.PairLeaves3_69

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

set_option maxHeartbeats 400000 in
theorem assembled_pair3_3 : pairSuffix3Depth1 3 = true := by
  unfold pairSuffix3Depth1
  apply allLe_intro
  intro b7 hb7
  norm_num at hb7
  have hb7_cases_upper : b7 ≤ 4 := by omega
  interval_cases b7
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 4 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 4 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 4 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_3_0_0_0_0_0_0_0
              · exact pair_leaf3_3_0_0_0_0_0_0_1
              · exact pair_leaf3_3_0_0_0_0_0_0_2
              · exact pair_leaf3_3_0_0_0_0_0_0_3
              · exact pair_leaf3_3_0_0_0_0_0_0_4
            · exact pair_leaf3_3_0_0_0_0_0_1
            · exact pair_leaf3_3_0_0_0_0_0_2
            · exact pair_leaf3_3_0_0_0_0_0_3
            · exact pair_leaf3_3_0_0_0_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_3_0_0_0_0_1_0
            · exact pair_leaf3_3_0_0_0_0_1_1
            · exact pair_leaf3_3_0_0_0_0_1_2
            · exact pair_leaf3_3_0_0_0_0_1_3
          · exact pair_leaf3_3_0_0_0_0_2
          · exact pair_leaf3_3_0_0_0_0_3
          · exact pair_leaf3_3_0_0_0_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_3_0_0_0_1_0_0
            · exact pair_leaf3_3_0_0_0_1_0_1
            · exact pair_leaf3_3_0_0_0_1_0_2
            · exact pair_leaf3_3_0_0_0_1_0_3
          · exact pair_leaf3_3_0_0_0_1_1
          · exact pair_leaf3_3_0_0_0_1_2
          · exact pair_leaf3_3_0_0_0_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_3_0_0_0_2_0
          · exact pair_leaf3_3_0_0_0_2_1
          · exact pair_leaf3_3_0_0_0_2_2
        · exact pair_leaf3_3_0_0_0_3
        · exact pair_leaf3_3_0_0_0_4
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 3 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_3_0_0_1_0_0_0
            · exact pair_leaf3_3_0_0_1_0_0_1
            · exact pair_leaf3_3_0_0_1_0_0_2
            · exact pair_leaf3_3_0_0_1_0_0_3
          · exact pair_leaf3_3_0_0_1_0_1
          · exact pair_leaf3_3_0_0_1_0_2
          · exact pair_leaf3_3_0_0_1_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_3_0_0_1_1_0
          · exact pair_leaf3_3_0_0_1_1_1
          · exact pair_leaf3_3_0_0_1_1_2
        · exact pair_leaf3_3_0_0_1_2
        · exact pair_leaf3_3_0_0_1_3
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
          · exact pair_leaf3_3_0_0_2_0_0
          · exact pair_leaf3_3_0_0_2_0_1
          · exact pair_leaf3_3_0_0_2_0_2
        · exact pair_leaf3_3_0_0_2_1
        · exact pair_leaf3_3_0_0_2_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_0_0_3_0
        · exact pair_leaf3_3_0_0_3_1
      · exact pair_leaf3_3_0_0_4
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 3 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 3 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_3_0_1_0_0_0_0
            · exact pair_leaf3_3_0_1_0_0_0_1
            · exact pair_leaf3_3_0_1_0_0_0_2
            · exact pair_leaf3_3_0_1_0_0_0_3
          · exact pair_leaf3_3_0_1_0_0_1
          · exact pair_leaf3_3_0_1_0_0_2
          · exact pair_leaf3_3_0_1_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_3_0_1_0_1_0
          · exact pair_leaf3_3_0_1_0_1_1
          · exact pair_leaf3_3_0_1_0_1_2
        · exact pair_leaf3_3_0_1_0_2
        · exact pair_leaf3_3_0_1_0_3
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
          · exact pair_leaf3_3_0_1_1_0_0
          · exact pair_leaf3_3_0_1_1_0_1
          · exact pair_leaf3_3_0_1_1_0_2
        · exact pair_leaf3_3_0_1_1_1
        · exact pair_leaf3_3_0_1_1_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_0_1_2_0
        · exact pair_leaf3_3_0_1_2_1
      · exact pair_leaf3_3_0_1_3
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
          · exact pair_leaf3_3_0_2_0_0_0
          · exact pair_leaf3_3_0_2_0_0_1
          · exact pair_leaf3_3_0_2_0_0_2
        · exact pair_leaf3_3_0_2_0_1
        · exact pair_leaf3_3_0_2_0_2
      · exact pair_leaf3_3_0_2_1
      · exact pair_leaf3_3_0_2_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_3_0_3_0
      · exact pair_leaf3_3_0_3_1
    · exact pair_leaf3_3_0_4
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 3 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 3 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 3 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_3_1_0_0_0_0_0
            · exact pair_leaf3_3_1_0_0_0_0_1
            · exact pair_leaf3_3_1_0_0_0_0_2
            · exact pair_leaf3_3_1_0_0_0_0_3
          · exact pair_leaf3_3_1_0_0_0_1
          · exact pair_leaf3_3_1_0_0_0_2
          · exact pair_leaf3_3_1_0_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_3_1_0_0_1_0
          · exact pair_leaf3_3_1_0_0_1_1
          · exact pair_leaf3_3_1_0_0_1_2
        · exact pair_leaf3_3_1_0_0_2
        · exact pair_leaf3_3_1_0_0_3
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
          · exact pair_leaf3_3_1_0_1_0_0
          · exact pair_leaf3_3_1_0_1_0_1
          · exact pair_leaf3_3_1_0_1_0_2
        · exact pair_leaf3_3_1_0_1_1
        · exact pair_leaf3_3_1_0_1_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_1_0_2_0
        · exact pair_leaf3_3_1_0_2_1
      · exact pair_leaf3_3_1_0_3
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
          · exact pair_leaf3_3_1_1_0_0_0
          · exact pair_leaf3_3_1_1_0_0_1
          · exact pair_leaf3_3_1_1_0_0_2
        · exact pair_leaf3_3_1_1_0_1
        · exact pair_leaf3_3_1_1_0_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_1_1_1_0
        · exact pair_leaf3_3_1_1_1_1
      · exact pair_leaf3_3_1_1_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_3_1_2_0
      · exact pair_leaf3_3_1_2_1
    · exact pair_leaf3_3_1_3
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
          · exact pair_leaf3_3_2_0_0_0_0
          · exact pair_leaf3_3_2_0_0_0_1
          · exact pair_leaf3_3_2_0_0_0_2
        · exact pair_leaf3_3_2_0_0_1
        · exact pair_leaf3_3_2_0_0_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_2_0_1_0
        · exact pair_leaf3_3_2_0_1_1
      · exact pair_leaf3_3_2_0_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_2_1_0_0
        · exact pair_leaf3_3_2_1_0_1
      · exact pair_leaf3_3_2_1_1
    · exact pair_leaf3_3_2_2
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
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_3_3_0_0_0
        · exact pair_leaf3_3_3_0_0_1
      · exact pair_leaf3_3_3_0_1
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 0 := by omega
      interval_cases b6
      · exact pair_leaf3_3_3_1_0
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 0 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 0 := by omega
      interval_cases b6
      · exact pair_leaf3_3_4_0_0

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.assembled_pair3_3
