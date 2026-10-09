import Research.Backfill.Paper6.PairLeaves3_00
import Research.Backfill.Paper6.PairLeaves3_01
import Research.Backfill.Paper6.PairLeaves3_02
import Research.Backfill.Paper6.PairLeaves3_03
import Research.Backfill.Paper6.PairLeaves3_04
import Research.Backfill.Paper6.PairLeaves3_05
import Research.Backfill.Paper6.PairLeaves3_06
import Research.Backfill.Paper6.PairLeaves3_07
import Research.Backfill.Paper6.PairLeaves3_08
import Research.Backfill.Paper6.PairLeaves3_09
import Research.Backfill.Paper6.PairLeaves3_10
import Research.Backfill.Paper6.PairLeaves3_11
import Research.Backfill.Paper6.PairLeaves3_12
import Research.Backfill.Paper6.PairLeaves3_13
import Research.Backfill.Paper6.PairLeaves3_14
import Research.Backfill.Paper6.PairLeaves3_15
import Research.Backfill.Paper6.PairLeaves3_16
import Research.Backfill.Paper6.PairLeaves3_17
import Research.Backfill.Paper6.PairLeaves3_18
import Research.Backfill.Paper6.PairLeaves3_19
import Research.Backfill.Paper6.PairLeaves3_20
import Research.Backfill.Paper6.PairLeaves3_21
import Research.Backfill.Paper6.PairLeaves3_22
import Research.Backfill.Paper6.PairLeaves3_23
import Research.Backfill.Paper6.PairLeaves3_24
import Research.Backfill.Paper6.PairLeaves3_25
import Research.Backfill.Paper6.PairLeaves3_26
import Research.Backfill.Paper6.PairLeaves3_27
import Research.Backfill.Paper6.PairLeaves3_28
import Research.Backfill.Paper6.PairLeaves3_29
import Research.Backfill.Paper6.PairLeaves3_30
import Research.Backfill.Paper6.PairLeaves3_31
import Research.Backfill.Paper6.PairLeaves3_32
import Research.Backfill.Paper6.PairLeaves3_33
import Research.Backfill.Paper6.PairLeaves3_34
import Research.Backfill.Paper6.PairLeaves3_35
import Research.Backfill.Paper6.PairLeaves3_36
import Research.Backfill.Paper6.PairLeaves3_37
import Research.Backfill.Paper6.PairLeaves3_38
import Research.Backfill.Paper6.PairLeaves3_39
import Research.Backfill.Paper6.PairLeaves3_40

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6FiveExclusion

set_option maxHeartbeats 400000 in
theorem assembled_pair3_0 : pairSuffix3Depth1 0 = true := by
  unfold pairSuffix3Depth1
  apply allLe_intro
  intro b7 hb7
  norm_num at hb7
  have hb7_cases_upper : b7 ≤ 7 := by omega
  interval_cases b7
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 7 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 7 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 7 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 7 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 7 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 7 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 7 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_0_0_0_0_0_0
                · exact pair_leaf3_0_0_0_0_0_0_0_0_1
                · exact pair_leaf3_0_0_0_0_0_0_0_0_2
                · exact pair_leaf3_0_0_0_0_0_0_0_0_3
                · exact pair_leaf3_0_0_0_0_0_0_0_0_4
                · exact pair_leaf3_0_0_0_0_0_0_0_0_5
                · exact pair_leaf3_0_0_0_0_0_0_0_0_6
                · exact pair_leaf3_0_0_0_0_0_0_0_0_7
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 7 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_0_0_0_0_1_0
                · exact pair_leaf3_0_0_0_0_0_0_0_1_1
                · exact pair_leaf3_0_0_0_0_0_0_0_1_2
                · exact pair_leaf3_0_0_0_0_0_0_0_1_3
                · exact pair_leaf3_0_0_0_0_0_0_0_1_4
                · exact pair_leaf3_0_0_0_0_0_0_0_1_5
                · exact pair_leaf3_0_0_0_0_0_0_0_1_6
                · exact pair_leaf3_0_0_0_0_0_0_0_1_7
              · exact pair_leaf3_0_0_0_0_0_0_0_2
              · exact pair_leaf3_0_0_0_0_0_0_0_3
              · exact pair_leaf3_0_0_0_0_0_0_0_4
              · exact pair_leaf3_0_0_0_0_0_0_0_5
              · exact pair_leaf3_0_0_0_0_0_0_0_6
              · exact pair_leaf3_0_0_0_0_0_0_0_7
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_0_0_0_1_0_0
                · exact pair_leaf3_0_0_0_0_0_0_1_0_1
                · exact pair_leaf3_0_0_0_0_0_0_1_0_2
                · exact pair_leaf3_0_0_0_0_0_0_1_0_3
                · exact pair_leaf3_0_0_0_0_0_0_1_0_4
                · exact pair_leaf3_0_0_0_0_0_0_1_0_5
                · exact pair_leaf3_0_0_0_0_0_0_1_0_6
              · exact pair_leaf3_0_0_0_0_0_0_1_1
              · exact pair_leaf3_0_0_0_0_0_0_1_2
              · exact pair_leaf3_0_0_0_0_0_0_1_3
              · exact pair_leaf3_0_0_0_0_0_0_1_4
              · exact pair_leaf3_0_0_0_0_0_0_1_5
              · exact pair_leaf3_0_0_0_0_0_0_1_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_0_2_0
              · exact pair_leaf3_0_0_0_0_0_0_2_1
              · exact pair_leaf3_0_0_0_0_0_0_2_2
              · exact pair_leaf3_0_0_0_0_0_0_2_3
              · exact pair_leaf3_0_0_0_0_0_0_2_4
              · exact pair_leaf3_0_0_0_0_0_0_2_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_0_3_0
              · exact pair_leaf3_0_0_0_0_0_0_3_1
              · exact pair_leaf3_0_0_0_0_0_0_3_2
              · exact pair_leaf3_0_0_0_0_0_0_3_3
              · exact pair_leaf3_0_0_0_0_0_0_3_4
            · exact pair_leaf3_0_0_0_0_0_0_4
            · exact pair_leaf3_0_0_0_0_0_0_5
            · exact pair_leaf3_0_0_0_0_0_0_6
            · exact pair_leaf3_0_0_0_0_0_0_7
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_0_0_1_0_0_0
                · exact pair_leaf3_0_0_0_0_0_1_0_0_1
                · exact pair_leaf3_0_0_0_0_0_1_0_0_2
                · exact pair_leaf3_0_0_0_0_0_1_0_0_3
                · exact pair_leaf3_0_0_0_0_0_1_0_0_4
                · exact pair_leaf3_0_0_0_0_0_1_0_0_5
                · exact pair_leaf3_0_0_0_0_0_1_0_0_6
              · exact pair_leaf3_0_0_0_0_0_1_0_1
              · exact pair_leaf3_0_0_0_0_0_1_0_2
              · exact pair_leaf3_0_0_0_0_0_1_0_3
              · exact pair_leaf3_0_0_0_0_0_1_0_4
              · exact pair_leaf3_0_0_0_0_0_1_0_5
              · exact pair_leaf3_0_0_0_0_0_1_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_1_1_0
              · exact pair_leaf3_0_0_0_0_0_1_1_1
              · exact pair_leaf3_0_0_0_0_0_1_1_2
              · exact pair_leaf3_0_0_0_0_0_1_1_3
              · exact pair_leaf3_0_0_0_0_0_1_1_4
              · exact pair_leaf3_0_0_0_0_0_1_1_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_1_2_0
              · exact pair_leaf3_0_0_0_0_0_1_2_1
              · exact pair_leaf3_0_0_0_0_0_1_2_2
              · exact pair_leaf3_0_0_0_0_0_1_2_3
              · exact pair_leaf3_0_0_0_0_0_1_2_4
            · exact pair_leaf3_0_0_0_0_0_1_3
            · exact pair_leaf3_0_0_0_0_0_1_4
            · exact pair_leaf3_0_0_0_0_0_1_5
            · exact pair_leaf3_0_0_0_0_0_1_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_2_0_0
              · exact pair_leaf3_0_0_0_0_0_2_0_1
              · exact pair_leaf3_0_0_0_0_0_2_0_2
              · exact pair_leaf3_0_0_0_0_0_2_0_3
              · exact pair_leaf3_0_0_0_0_0_2_0_4
              · exact pair_leaf3_0_0_0_0_0_2_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_0_2_1_0
              · exact pair_leaf3_0_0_0_0_0_2_1_1
              · exact pair_leaf3_0_0_0_0_0_2_1_2
              · exact pair_leaf3_0_0_0_0_0_2_1_3
              · exact pair_leaf3_0_0_0_0_0_2_1_4
            · exact pair_leaf3_0_0_0_0_0_2_2
            · exact pair_leaf3_0_0_0_0_0_2_3
            · exact pair_leaf3_0_0_0_0_0_2_4
            · exact pair_leaf3_0_0_0_0_0_2_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_0_0_3_0
            · exact pair_leaf3_0_0_0_0_0_3_1
            · exact pair_leaf3_0_0_0_0_0_3_2
            · exact pair_leaf3_0_0_0_0_0_3_3
            · exact pair_leaf3_0_0_0_0_0_3_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_0_0_4_0
            · exact pair_leaf3_0_0_0_0_0_4_1
            · exact pair_leaf3_0_0_0_0_0_4_2
            · exact pair_leaf3_0_0_0_0_0_4_3
          · exact pair_leaf3_0_0_0_0_0_5
          · exact pair_leaf3_0_0_0_0_0_6
          · exact pair_leaf3_0_0_0_0_0_7
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 6 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_0_1_0_0_0_0
                · exact pair_leaf3_0_0_0_0_1_0_0_0_1
                · exact pair_leaf3_0_0_0_0_1_0_0_0_2
                · exact pair_leaf3_0_0_0_0_1_0_0_0_3
                · exact pair_leaf3_0_0_0_0_1_0_0_0_4
                · exact pair_leaf3_0_0_0_0_1_0_0_0_5
                · exact pair_leaf3_0_0_0_0_1_0_0_0_6
              · exact pair_leaf3_0_0_0_0_1_0_0_1
              · exact pair_leaf3_0_0_0_0_1_0_0_2
              · exact pair_leaf3_0_0_0_0_1_0_0_3
              · exact pair_leaf3_0_0_0_0_1_0_0_4
              · exact pair_leaf3_0_0_0_0_1_0_0_5
              · exact pair_leaf3_0_0_0_0_1_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_1_0_1_0
              · exact pair_leaf3_0_0_0_0_1_0_1_1
              · exact pair_leaf3_0_0_0_0_1_0_1_2
              · exact pair_leaf3_0_0_0_0_1_0_1_3
              · exact pair_leaf3_0_0_0_0_1_0_1_4
              · exact pair_leaf3_0_0_0_0_1_0_1_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_1_0_2_0
              · exact pair_leaf3_0_0_0_0_1_0_2_1
              · exact pair_leaf3_0_0_0_0_1_0_2_2
              · exact pair_leaf3_0_0_0_0_1_0_2_3
              · exact pair_leaf3_0_0_0_0_1_0_2_4
            · exact pair_leaf3_0_0_0_0_1_0_3
            · exact pair_leaf3_0_0_0_0_1_0_4
            · exact pair_leaf3_0_0_0_0_1_0_5
            · exact pair_leaf3_0_0_0_0_1_0_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_1_1_0_0
              · exact pair_leaf3_0_0_0_0_1_1_0_1
              · exact pair_leaf3_0_0_0_0_1_1_0_2
              · exact pair_leaf3_0_0_0_0_1_1_0_3
              · exact pair_leaf3_0_0_0_0_1_1_0_4
              · exact pair_leaf3_0_0_0_0_1_1_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_1_1_1_0
              · exact pair_leaf3_0_0_0_0_1_1_1_1
              · exact pair_leaf3_0_0_0_0_1_1_1_2
              · exact pair_leaf3_0_0_0_0_1_1_1_3
              · exact pair_leaf3_0_0_0_0_1_1_1_4
            · exact pair_leaf3_0_0_0_0_1_1_2
            · exact pair_leaf3_0_0_0_0_1_1_3
            · exact pair_leaf3_0_0_0_0_1_1_4
            · exact pair_leaf3_0_0_0_0_1_1_5
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
              · exact pair_leaf3_0_0_0_0_1_2_0_0
              · exact pair_leaf3_0_0_0_0_1_2_0_1
              · exact pair_leaf3_0_0_0_0_1_2_0_2
              · exact pair_leaf3_0_0_0_0_1_2_0_3
              · exact pair_leaf3_0_0_0_0_1_2_0_4
            · exact pair_leaf3_0_0_0_0_1_2_1
            · exact pair_leaf3_0_0_0_0_1_2_2
            · exact pair_leaf3_0_0_0_0_1_2_3
            · exact pair_leaf3_0_0_0_0_1_2_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_0_1_3_0
            · exact pair_leaf3_0_0_0_0_1_3_1
            · exact pair_leaf3_0_0_0_0_1_3_2
            · exact pair_leaf3_0_0_0_0_1_3_3
          · exact pair_leaf3_0_0_0_0_1_4
          · exact pair_leaf3_0_0_0_0_1_5
          · exact pair_leaf3_0_0_0_0_1_6
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_2_0_0_0
              · exact pair_leaf3_0_0_0_0_2_0_0_1
              · exact pair_leaf3_0_0_0_0_2_0_0_2
              · exact pair_leaf3_0_0_0_0_2_0_0_3
              · exact pair_leaf3_0_0_0_0_2_0_0_4
              · exact pair_leaf3_0_0_0_0_2_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_0_2_0_1_0
              · exact pair_leaf3_0_0_0_0_2_0_1_1
              · exact pair_leaf3_0_0_0_0_2_0_1_2
              · exact pair_leaf3_0_0_0_0_2_0_1_3
              · exact pair_leaf3_0_0_0_0_2_0_1_4
            · exact pair_leaf3_0_0_0_0_2_0_2
            · exact pair_leaf3_0_0_0_0_2_0_3
            · exact pair_leaf3_0_0_0_0_2_0_4
            · exact pair_leaf3_0_0_0_0_2_0_5
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
              · exact pair_leaf3_0_0_0_0_2_1_0_0
              · exact pair_leaf3_0_0_0_0_2_1_0_1
              · exact pair_leaf3_0_0_0_0_2_1_0_2
              · exact pair_leaf3_0_0_0_0_2_1_0_3
              · exact pair_leaf3_0_0_0_0_2_1_0_4
            · exact pair_leaf3_0_0_0_0_2_1_1
            · exact pair_leaf3_0_0_0_0_2_1_2
            · exact pair_leaf3_0_0_0_0_2_1_3
            · exact pair_leaf3_0_0_0_0_2_1_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_0_2_2_0
            · exact pair_leaf3_0_0_0_0_2_2_1
            · exact pair_leaf3_0_0_0_0_2_2_2
            · exact pair_leaf3_0_0_0_0_2_2_3
          · exact pair_leaf3_0_0_0_0_2_3
          · exact pair_leaf3_0_0_0_0_2_4
          · exact pair_leaf3_0_0_0_0_2_5
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
              · exact pair_leaf3_0_0_0_0_3_0_0_0
              · exact pair_leaf3_0_0_0_0_3_0_0_1
              · exact pair_leaf3_0_0_0_0_3_0_0_2
              · exact pair_leaf3_0_0_0_0_3_0_0_3
              · exact pair_leaf3_0_0_0_0_3_0_0_4
            · exact pair_leaf3_0_0_0_0_3_0_1
            · exact pair_leaf3_0_0_0_0_3_0_2
            · exact pair_leaf3_0_0_0_0_3_0_3
            · exact pair_leaf3_0_0_0_0_3_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_0_3_1_0
            · exact pair_leaf3_0_0_0_0_3_1_1
            · exact pair_leaf3_0_0_0_0_3_1_2
            · exact pair_leaf3_0_0_0_0_3_1_3
          · exact pair_leaf3_0_0_0_0_3_2
          · exact pair_leaf3_0_0_0_0_3_3
          · exact pair_leaf3_0_0_0_0_3_4
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
            · exact pair_leaf3_0_0_0_0_4_0_0
            · exact pair_leaf3_0_0_0_0_4_0_1
            · exact pair_leaf3_0_0_0_0_4_0_2
            · exact pair_leaf3_0_0_0_0_4_0_3
          · exact pair_leaf3_0_0_0_0_4_1
          · exact pair_leaf3_0_0_0_0_4_2
          · exact pair_leaf3_0_0_0_0_4_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_0_0_5_0
          · exact pair_leaf3_0_0_0_0_5_1
          · exact pair_leaf3_0_0_0_0_5_2
        · exact pair_leaf3_0_0_0_0_6
        · exact pair_leaf3_0_0_0_0_7
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 6 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 6 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_0_1_0_0_0_0_0
                · exact pair_leaf3_0_0_0_1_0_0_0_0_1
                · exact pair_leaf3_0_0_0_1_0_0_0_0_2
                · exact pair_leaf3_0_0_0_1_0_0_0_0_3
                · exact pair_leaf3_0_0_0_1_0_0_0_0_4
                · exact pair_leaf3_0_0_0_1_0_0_0_0_5
                · exact pair_leaf3_0_0_0_1_0_0_0_0_6
              · exact pair_leaf3_0_0_0_1_0_0_0_1
              · exact pair_leaf3_0_0_0_1_0_0_0_2
              · exact pair_leaf3_0_0_0_1_0_0_0_3
              · exact pair_leaf3_0_0_0_1_0_0_0_4
              · exact pair_leaf3_0_0_0_1_0_0_0_5
              · exact pair_leaf3_0_0_0_1_0_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_0_0_1_0
              · exact pair_leaf3_0_0_0_1_0_0_1_1
              · exact pair_leaf3_0_0_0_1_0_0_1_2
              · exact pair_leaf3_0_0_0_1_0_0_1_3
              · exact pair_leaf3_0_0_0_1_0_0_1_4
              · exact pair_leaf3_0_0_0_1_0_0_1_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_0_0_2_0
              · exact pair_leaf3_0_0_0_1_0_0_2_1
              · exact pair_leaf3_0_0_0_1_0_0_2_2
              · exact pair_leaf3_0_0_0_1_0_0_2_3
              · exact pair_leaf3_0_0_0_1_0_0_2_4
            · exact pair_leaf3_0_0_0_1_0_0_3
            · exact pair_leaf3_0_0_0_1_0_0_4
            · exact pair_leaf3_0_0_0_1_0_0_5
            · exact pair_leaf3_0_0_0_1_0_0_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_0_1_0_0
              · exact pair_leaf3_0_0_0_1_0_1_0_1
              · exact pair_leaf3_0_0_0_1_0_1_0_2
              · exact pair_leaf3_0_0_0_1_0_1_0_3
              · exact pair_leaf3_0_0_0_1_0_1_0_4
              · exact pair_leaf3_0_0_0_1_0_1_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_0_1_1_0
              · exact pair_leaf3_0_0_0_1_0_1_1_1
              · exact pair_leaf3_0_0_0_1_0_1_1_2
              · exact pair_leaf3_0_0_0_1_0_1_1_3
              · exact pair_leaf3_0_0_0_1_0_1_1_4
              · exact pair_leaf3_0_0_0_1_0_1_1_5
            · exact pair_leaf3_0_0_0_1_0_1_2
            · exact pair_leaf3_0_0_0_1_0_1_3
            · exact pair_leaf3_0_0_0_1_0_1_4
            · exact pair_leaf3_0_0_0_1_0_1_5
            · exact pair_leaf3_0_0_0_1_0_1_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_1_0_2_0
            · exact pair_leaf3_0_0_0_1_0_2_1
            · exact pair_leaf3_0_0_0_1_0_2_2
            · exact pair_leaf3_0_0_0_1_0_2_3
            · exact pair_leaf3_0_0_0_1_0_2_4
            · exact pair_leaf3_0_0_0_1_0_2_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_1_0_3_0
            · exact pair_leaf3_0_0_0_1_0_3_1
            · exact pair_leaf3_0_0_0_1_0_3_2
            · exact pair_leaf3_0_0_0_1_0_3_3
            · exact pair_leaf3_0_0_0_1_0_3_4
          · exact pair_leaf3_0_0_0_1_0_4
          · exact pair_leaf3_0_0_0_1_0_5
          · exact pair_leaf3_0_0_0_1_0_6
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_1_0_0_0
              · exact pair_leaf3_0_0_0_1_1_0_0_1
              · exact pair_leaf3_0_0_0_1_1_0_0_2
              · exact pair_leaf3_0_0_0_1_1_0_0_3
              · exact pair_leaf3_0_0_0_1_1_0_0_4
              · exact pair_leaf3_0_0_0_1_1_0_0_5
              · exact pair_leaf3_0_0_0_1_1_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_1_0_1_0
              · exact pair_leaf3_0_0_0_1_1_0_1_1
              · exact pair_leaf3_0_0_0_1_1_0_1_2
              · exact pair_leaf3_0_0_0_1_1_0_1_3
              · exact pair_leaf3_0_0_0_1_1_0_1_4
              · exact pair_leaf3_0_0_0_1_1_0_1_5
            · exact pair_leaf3_0_0_0_1_1_0_2
            · exact pair_leaf3_0_0_0_1_1_0_3
            · exact pair_leaf3_0_0_0_1_1_0_4
            · exact pair_leaf3_0_0_0_1_1_0_5
            · exact pair_leaf3_0_0_0_1_1_0_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_1_1_0_0
              · exact pair_leaf3_0_0_0_1_1_1_0_1
              · exact pair_leaf3_0_0_0_1_1_1_0_2
              · exact pair_leaf3_0_0_0_1_1_1_0_3
              · exact pair_leaf3_0_0_0_1_1_1_0_4
              · exact pair_leaf3_0_0_0_1_1_1_0_5
            · exact pair_leaf3_0_0_0_1_1_1_1
            · exact pair_leaf3_0_0_0_1_1_1_2
            · exact pair_leaf3_0_0_0_1_1_1_3
            · exact pair_leaf3_0_0_0_1_1_1_4
            · exact pair_leaf3_0_0_0_1_1_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_1_1_2_0
            · exact pair_leaf3_0_0_0_1_1_2_1
            · exact pair_leaf3_0_0_0_1_1_2_2
            · exact pair_leaf3_0_0_0_1_1_2_3
            · exact pair_leaf3_0_0_0_1_1_2_4
          · exact pair_leaf3_0_0_0_1_1_3
          · exact pair_leaf3_0_0_0_1_1_4
          · exact pair_leaf3_0_0_0_1_1_5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_1_2_0_0_0
              · exact pair_leaf3_0_0_0_1_2_0_0_1
              · exact pair_leaf3_0_0_0_1_2_0_0_2
              · exact pair_leaf3_0_0_0_1_2_0_0_3
              · exact pair_leaf3_0_0_0_1_2_0_0_4
              · exact pair_leaf3_0_0_0_1_2_0_0_5
            · exact pair_leaf3_0_0_0_1_2_0_1
            · exact pair_leaf3_0_0_0_1_2_0_2
            · exact pair_leaf3_0_0_0_1_2_0_3
            · exact pair_leaf3_0_0_0_1_2_0_4
            · exact pair_leaf3_0_0_0_1_2_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_1_2_1_0
            · exact pair_leaf3_0_0_0_1_2_1_1
            · exact pair_leaf3_0_0_0_1_2_1_2
            · exact pair_leaf3_0_0_0_1_2_1_3
            · exact pair_leaf3_0_0_0_1_2_1_4
          · exact pair_leaf3_0_0_0_1_2_2
          · exact pair_leaf3_0_0_0_1_2_3
          · exact pair_leaf3_0_0_0_1_2_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_1_3_0_0
            · exact pair_leaf3_0_0_0_1_3_0_1
            · exact pair_leaf3_0_0_0_1_3_0_2
            · exact pair_leaf3_0_0_0_1_3_0_3
            · exact pair_leaf3_0_0_0_1_3_0_4
          · exact pair_leaf3_0_0_0_1_3_1
          · exact pair_leaf3_0_0_0_1_3_2
          · exact pair_leaf3_0_0_0_1_3_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_0_1_4_0
          · exact pair_leaf3_0_0_0_1_4_1
          · exact pair_leaf3_0_0_0_1_4_2
        · exact pair_leaf3_0_0_0_1_5
        · exact pair_leaf3_0_0_0_1_6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_2_0_0_0_0
              · exact pair_leaf3_0_0_0_2_0_0_0_1
              · exact pair_leaf3_0_0_0_2_0_0_0_2
              · exact pair_leaf3_0_0_0_2_0_0_0_3
              · exact pair_leaf3_0_0_0_2_0_0_0_4
              · exact pair_leaf3_0_0_0_2_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_2_0_0_1_0
              · exact pair_leaf3_0_0_0_2_0_0_1_1
              · exact pair_leaf3_0_0_0_2_0_0_1_2
              · exact pair_leaf3_0_0_0_2_0_0_1_3
              · exact pair_leaf3_0_0_0_2_0_0_1_4
            · exact pair_leaf3_0_0_0_2_0_0_2
            · exact pair_leaf3_0_0_0_2_0_0_3
            · exact pair_leaf3_0_0_0_2_0_0_4
            · exact pair_leaf3_0_0_0_2_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_2_0_1_0
            · exact pair_leaf3_0_0_0_2_0_1_1
            · exact pair_leaf3_0_0_0_2_0_1_2
            · exact pair_leaf3_0_0_0_2_0_1_3
            · exact pair_leaf3_0_0_0_2_0_1_4
            · exact pair_leaf3_0_0_0_2_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_2_0_2_0
            · exact pair_leaf3_0_0_0_2_0_2_1
            · exact pair_leaf3_0_0_0_2_0_2_2
            · exact pair_leaf3_0_0_0_2_0_2_3
            · exact pair_leaf3_0_0_0_2_0_2_4
            · exact pair_leaf3_0_0_0_2_0_2_5
          · exact pair_leaf3_0_0_0_2_0_3
          · exact pair_leaf3_0_0_0_2_0_4
          · exact pair_leaf3_0_0_0_2_0_5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_0_2_1_0_0_0
              · exact pair_leaf3_0_0_0_2_1_0_0_1
              · exact pair_leaf3_0_0_0_2_1_0_0_2
              · exact pair_leaf3_0_0_0_2_1_0_0_3
              · exact pair_leaf3_0_0_0_2_1_0_0_4
              · exact pair_leaf3_0_0_0_2_1_0_0_5
            · exact pair_leaf3_0_0_0_2_1_0_1
            · exact pair_leaf3_0_0_0_2_1_0_2
            · exact pair_leaf3_0_0_0_2_1_0_3
            · exact pair_leaf3_0_0_0_2_1_0_4
            · exact pair_leaf3_0_0_0_2_1_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_2_1_1_0
            · exact pair_leaf3_0_0_0_2_1_1_1
            · exact pair_leaf3_0_0_0_2_1_1_2
            · exact pair_leaf3_0_0_0_2_1_1_3
            · exact pair_leaf3_0_0_0_2_1_1_4
            · exact pair_leaf3_0_0_0_2_1_1_5
          · exact pair_leaf3_0_0_0_2_1_2
          · exact pair_leaf3_0_0_0_2_1_3
          · exact pair_leaf3_0_0_0_2_1_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_2_2_0_0
            · exact pair_leaf3_0_0_0_2_2_0_1
            · exact pair_leaf3_0_0_0_2_2_0_2
            · exact pair_leaf3_0_0_0_2_2_0_3
            · exact pair_leaf3_0_0_0_2_2_0_4
            · exact pair_leaf3_0_0_0_2_2_0_5
          · exact pair_leaf3_0_0_0_2_2_1
          · exact pair_leaf3_0_0_0_2_2_2
          · exact pair_leaf3_0_0_0_2_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_0_2_3_0
          · exact pair_leaf3_0_0_0_2_3_1
          · exact pair_leaf3_0_0_0_2_3_2
        · exact pair_leaf3_0_0_0_2_4
        · exact pair_leaf3_0_0_0_2_5
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
            · exact pair_leaf3_0_0_0_3_0_0_0
            · exact pair_leaf3_0_0_0_3_0_0_1
            · exact pair_leaf3_0_0_0_3_0_0_2
            · exact pair_leaf3_0_0_0_3_0_0_3
            · exact pair_leaf3_0_0_0_3_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_3_0_1_0
            · exact pair_leaf3_0_0_0_3_0_1_1
            · exact pair_leaf3_0_0_0_3_0_1_2
            · exact pair_leaf3_0_0_0_3_0_1_3
            · exact pair_leaf3_0_0_0_3_0_1_4
          · exact pair_leaf3_0_0_0_3_0_2
          · exact pair_leaf3_0_0_0_3_0_3
          · exact pair_leaf3_0_0_0_3_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_0_3_1_0_0
            · exact pair_leaf3_0_0_0_3_1_0_1
            · exact pair_leaf3_0_0_0_3_1_0_2
            · exact pair_leaf3_0_0_0_3_1_0_3
            · exact pair_leaf3_0_0_0_3_1_0_4
          · exact pair_leaf3_0_0_0_3_1_1
          · exact pair_leaf3_0_0_0_3_1_2
          · exact pair_leaf3_0_0_0_3_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_0_3_2_0
          · exact pair_leaf3_0_0_0_3_2_1
          · exact pair_leaf3_0_0_0_3_2_2
        · exact pair_leaf3_0_0_0_3_3
        · exact pair_leaf3_0_0_0_3_4
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
            · exact pair_leaf3_0_0_0_4_0_0_0
            · exact pair_leaf3_0_0_0_4_0_0_1
            · exact pair_leaf3_0_0_0_4_0_0_2
            · exact pair_leaf3_0_0_0_4_0_0_3
          · exact pair_leaf3_0_0_0_4_0_1
          · exact pair_leaf3_0_0_0_4_0_2
          · exact pair_leaf3_0_0_0_4_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_0_4_1_0
          · exact pair_leaf3_0_0_0_4_1_1
          · exact pair_leaf3_0_0_0_4_1_2
        · exact pair_leaf3_0_0_0_4_2
        · exact pair_leaf3_0_0_0_4_3
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · exact pair_leaf3_0_0_0_5_0
        · exact pair_leaf3_0_0_0_5_1
        · exact pair_leaf3_0_0_0_5_2
      · exact pair_leaf3_0_0_0_6
      · exact pair_leaf3_0_0_0_7
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 6 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 6 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 6 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_0_1_0_0_0_0_0_0
                · exact pair_leaf3_0_0_1_0_0_0_0_0_1
                · exact pair_leaf3_0_0_1_0_0_0_0_0_2
                · exact pair_leaf3_0_0_1_0_0_0_0_0_3
                · exact pair_leaf3_0_0_1_0_0_0_0_0_4
                · exact pair_leaf3_0_0_1_0_0_0_0_0_5
                · exact pair_leaf3_0_0_1_0_0_0_0_0_6
              · exact pair_leaf3_0_0_1_0_0_0_0_1
              · exact pair_leaf3_0_0_1_0_0_0_0_2
              · exact pair_leaf3_0_0_1_0_0_0_0_3
              · exact pair_leaf3_0_0_1_0_0_0_0_4
              · exact pair_leaf3_0_0_1_0_0_0_0_5
              · exact pair_leaf3_0_0_1_0_0_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_0_0_1_0
              · exact pair_leaf3_0_0_1_0_0_0_1_1
              · exact pair_leaf3_0_0_1_0_0_0_1_2
              · exact pair_leaf3_0_0_1_0_0_0_1_3
              · exact pair_leaf3_0_0_1_0_0_0_1_4
              · exact pair_leaf3_0_0_1_0_0_0_1_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_0_0_2_0
              · exact pair_leaf3_0_0_1_0_0_0_2_1
              · exact pair_leaf3_0_0_1_0_0_0_2_2
              · exact pair_leaf3_0_0_1_0_0_0_2_3
              · exact pair_leaf3_0_0_1_0_0_0_2_4
            · exact pair_leaf3_0_0_1_0_0_0_3
            · exact pair_leaf3_0_0_1_0_0_0_4
            · exact pair_leaf3_0_0_1_0_0_0_5
            · exact pair_leaf3_0_0_1_0_0_0_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_0_1_0_0
              · exact pair_leaf3_0_0_1_0_0_1_0_1
              · exact pair_leaf3_0_0_1_0_0_1_0_2
              · exact pair_leaf3_0_0_1_0_0_1_0_3
              · exact pair_leaf3_0_0_1_0_0_1_0_4
              · exact pair_leaf3_0_0_1_0_0_1_0_5
              · exact pair_leaf3_0_0_1_0_0_1_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_0_1_1_0
              · exact pair_leaf3_0_0_1_0_0_1_1_1
              · exact pair_leaf3_0_0_1_0_0_1_1_2
              · exact pair_leaf3_0_0_1_0_0_1_1_3
              · exact pair_leaf3_0_0_1_0_0_1_1_4
              · exact pair_leaf3_0_0_1_0_0_1_1_5
            · exact pair_leaf3_0_0_1_0_0_1_2
            · exact pair_leaf3_0_0_1_0_0_1_3
            · exact pair_leaf3_0_0_1_0_0_1_4
            · exact pair_leaf3_0_0_1_0_0_1_5
            · exact pair_leaf3_0_0_1_0_0_1_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_0_2_0_0
              · exact pair_leaf3_0_0_1_0_0_2_0_1
              · exact pair_leaf3_0_0_1_0_0_2_0_2
              · exact pair_leaf3_0_0_1_0_0_2_0_3
              · exact pair_leaf3_0_0_1_0_0_2_0_4
              · exact pair_leaf3_0_0_1_0_0_2_0_5
            · exact pair_leaf3_0_0_1_0_0_2_1
            · exact pair_leaf3_0_0_1_0_0_2_2
            · exact pair_leaf3_0_0_1_0_0_2_3
            · exact pair_leaf3_0_0_1_0_0_2_4
            · exact pair_leaf3_0_0_1_0_0_2_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_0_0_3_0
            · exact pair_leaf3_0_0_1_0_0_3_1
            · exact pair_leaf3_0_0_1_0_0_3_2
            · exact pair_leaf3_0_0_1_0_0_3_3
            · exact pair_leaf3_0_0_1_0_0_3_4
          · exact pair_leaf3_0_0_1_0_0_4
          · exact pair_leaf3_0_0_1_0_0_5
          · exact pair_leaf3_0_0_1_0_0_6
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_1_0_0_0
              · exact pair_leaf3_0_0_1_0_1_0_0_1
              · exact pair_leaf3_0_0_1_0_1_0_0_2
              · exact pair_leaf3_0_0_1_0_1_0_0_3
              · exact pair_leaf3_0_0_1_0_1_0_0_4
              · exact pair_leaf3_0_0_1_0_1_0_0_5
              · exact pair_leaf3_0_0_1_0_1_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_1_0_1_0
              · exact pair_leaf3_0_0_1_0_1_0_1_1
              · exact pair_leaf3_0_0_1_0_1_0_1_2
              · exact pair_leaf3_0_0_1_0_1_0_1_3
              · exact pair_leaf3_0_0_1_0_1_0_1_4
              · exact pair_leaf3_0_0_1_0_1_0_1_5
            · exact pair_leaf3_0_0_1_0_1_0_2
            · exact pair_leaf3_0_0_1_0_1_0_3
            · exact pair_leaf3_0_0_1_0_1_0_4
            · exact pair_leaf3_0_0_1_0_1_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_1_1_0_0
              · exact pair_leaf3_0_0_1_0_1_1_0_1
              · exact pair_leaf3_0_0_1_0_1_1_0_2
              · exact pair_leaf3_0_0_1_0_1_1_0_3
              · exact pair_leaf3_0_0_1_0_1_1_0_4
              · exact pair_leaf3_0_0_1_0_1_1_0_5
            · exact pair_leaf3_0_0_1_0_1_1_1
            · exact pair_leaf3_0_0_1_0_1_1_2
            · exact pair_leaf3_0_0_1_0_1_1_3
            · exact pair_leaf3_0_0_1_0_1_1_4
            · exact pair_leaf3_0_0_1_0_1_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_0_1_2_0
            · exact pair_leaf3_0_0_1_0_1_2_1
            · exact pair_leaf3_0_0_1_0_1_2_2
            · exact pair_leaf3_0_0_1_0_1_2_3
            · exact pair_leaf3_0_0_1_0_1_2_4
          · exact pair_leaf3_0_0_1_0_1_3
          · exact pair_leaf3_0_0_1_0_1_4
          · exact pair_leaf3_0_0_1_0_1_5
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
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_0_2_0_0_0
              · exact pair_leaf3_0_0_1_0_2_0_0_1
              · exact pair_leaf3_0_0_1_0_2_0_0_2
              · exact pair_leaf3_0_0_1_0_2_0_0_3
              · exact pair_leaf3_0_0_1_0_2_0_0_4
              · exact pair_leaf3_0_0_1_0_2_0_0_5
            · exact pair_leaf3_0_0_1_0_2_0_1
            · exact pair_leaf3_0_0_1_0_2_0_2
            · exact pair_leaf3_0_0_1_0_2_0_3
            · exact pair_leaf3_0_0_1_0_2_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_0_2_1_0
            · exact pair_leaf3_0_0_1_0_2_1_1
            · exact pair_leaf3_0_0_1_0_2_1_2
            · exact pair_leaf3_0_0_1_0_2_1_3
            · exact pair_leaf3_0_0_1_0_2_1_4
          · exact pair_leaf3_0_0_1_0_2_2
          · exact pair_leaf3_0_0_1_0_2_3
          · exact pair_leaf3_0_0_1_0_2_4
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
            · exact pair_leaf3_0_0_1_0_3_0_0
            · exact pair_leaf3_0_0_1_0_3_0_1
            · exact pair_leaf3_0_0_1_0_3_0_2
            · exact pair_leaf3_0_0_1_0_3_0_3
          · exact pair_leaf3_0_0_1_0_3_1
          · exact pair_leaf3_0_0_1_0_3_2
          · exact pair_leaf3_0_0_1_0_3_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_1_0_4_0
          · exact pair_leaf3_0_0_1_0_4_1
          · exact pair_leaf3_0_0_1_0_4_2
        · exact pair_leaf3_0_0_1_0_5
        · exact pair_leaf3_0_0_1_0_6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_1_0_0_0_0
              · exact pair_leaf3_0_0_1_1_0_0_0_1
              · exact pair_leaf3_0_0_1_1_0_0_0_2
              · exact pair_leaf3_0_0_1_1_0_0_0_3
              · exact pair_leaf3_0_0_1_1_0_0_0_4
              · exact pair_leaf3_0_0_1_1_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_1_0_0_1_0
              · exact pair_leaf3_0_0_1_1_0_0_1_1
              · exact pair_leaf3_0_0_1_1_0_0_1_2
              · exact pair_leaf3_0_0_1_1_0_0_1_3
              · exact pair_leaf3_0_0_1_1_0_0_1_4
            · exact pair_leaf3_0_0_1_1_0_0_2
            · exact pair_leaf3_0_0_1_1_0_0_3
            · exact pair_leaf3_0_0_1_1_0_0_4
            · exact pair_leaf3_0_0_1_1_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_1_0_1_0_0
              · exact pair_leaf3_0_0_1_1_0_1_0_1
              · exact pair_leaf3_0_0_1_1_0_1_0_2
              · exact pair_leaf3_0_0_1_1_0_1_0_3
              · exact pair_leaf3_0_0_1_1_0_1_0_4
              · exact pair_leaf3_0_0_1_1_0_1_0_5
            · exact pair_leaf3_0_0_1_1_0_1_1
            · exact pair_leaf3_0_0_1_1_0_1_2
            · exact pair_leaf3_0_0_1_1_0_1_3
            · exact pair_leaf3_0_0_1_1_0_1_4
            · exact pair_leaf3_0_0_1_1_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_1_0_2_0
            · exact pair_leaf3_0_0_1_1_0_2_1
            · exact pair_leaf3_0_0_1_1_0_2_2
            · exact pair_leaf3_0_0_1_1_0_2_3
            · exact pair_leaf3_0_0_1_1_0_2_4
            · exact pair_leaf3_0_0_1_1_0_2_5
          · exact pair_leaf3_0_0_1_1_0_3
          · exact pair_leaf3_0_0_1_1_0_4
          · exact pair_leaf3_0_0_1_1_0_5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_1_1_1_0_0_0
              · exact pair_leaf3_0_0_1_1_1_0_0_1
              · exact pair_leaf3_0_0_1_1_1_0_0_2
              · exact pair_leaf3_0_0_1_1_1_0_0_3
              · exact pair_leaf3_0_0_1_1_1_0_0_4
              · exact pair_leaf3_0_0_1_1_1_0_0_5
            · exact pair_leaf3_0_0_1_1_1_0_1
            · exact pair_leaf3_0_0_1_1_1_0_2
            · exact pair_leaf3_0_0_1_1_1_0_3
            · exact pair_leaf3_0_0_1_1_1_0_4
            · exact pair_leaf3_0_0_1_1_1_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_1_1_1_0
            · exact pair_leaf3_0_0_1_1_1_1_1
            · exact pair_leaf3_0_0_1_1_1_1_2
            · exact pair_leaf3_0_0_1_1_1_1_3
            · exact pair_leaf3_0_0_1_1_1_1_4
            · exact pair_leaf3_0_0_1_1_1_1_5
          · exact pair_leaf3_0_0_1_1_1_2
          · exact pair_leaf3_0_0_1_1_1_3
          · exact pair_leaf3_0_0_1_1_1_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_1_2_0_0
            · exact pair_leaf3_0_0_1_1_2_0_1
            · exact pair_leaf3_0_0_1_1_2_0_2
            · exact pair_leaf3_0_0_1_1_2_0_3
            · exact pair_leaf3_0_0_1_1_2_0_4
          · exact pair_leaf3_0_0_1_1_2_1
          · exact pair_leaf3_0_0_1_1_2_2
          · exact pair_leaf3_0_0_1_1_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_1_1_3_0
          · exact pair_leaf3_0_0_1_1_3_1
          · exact pair_leaf3_0_0_1_1_3_2
        · exact pair_leaf3_0_0_1_1_4
        · exact pair_leaf3_0_0_1_1_5
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
              · exact pair_leaf3_0_0_1_2_0_0_0_0
              · exact pair_leaf3_0_0_1_2_0_0_0_1
              · exact pair_leaf3_0_0_1_2_0_0_0_2
              · exact pair_leaf3_0_0_1_2_0_0_0_3
              · exact pair_leaf3_0_0_1_2_0_0_0_4
            · exact pair_leaf3_0_0_1_2_0_0_1
            · exact pair_leaf3_0_0_1_2_0_0_2
            · exact pair_leaf3_0_0_1_2_0_0_3
            · exact pair_leaf3_0_0_1_2_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_2_0_1_0
            · exact pair_leaf3_0_0_1_2_0_1_1
            · exact pair_leaf3_0_0_1_2_0_1_2
            · exact pair_leaf3_0_0_1_2_0_1_3
            · exact pair_leaf3_0_0_1_2_0_1_4
          · exact pair_leaf3_0_0_1_2_0_2
          · exact pair_leaf3_0_0_1_2_0_3
          · exact pair_leaf3_0_0_1_2_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_1_2_1_0_0
            · exact pair_leaf3_0_0_1_2_1_0_1
            · exact pair_leaf3_0_0_1_2_1_0_2
            · exact pair_leaf3_0_0_1_2_1_0_3
            · exact pair_leaf3_0_0_1_2_1_0_4
          · exact pair_leaf3_0_0_1_2_1_1
          · exact pair_leaf3_0_0_1_2_1_2
          · exact pair_leaf3_0_0_1_2_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_1_2_2_0
          · exact pair_leaf3_0_0_1_2_2_1
          · exact pair_leaf3_0_0_1_2_2_2
        · exact pair_leaf3_0_0_1_2_3
        · exact pair_leaf3_0_0_1_2_4
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
            · exact pair_leaf3_0_0_1_3_0_0_0
            · exact pair_leaf3_0_0_1_3_0_0_1
            · exact pair_leaf3_0_0_1_3_0_0_2
            · exact pair_leaf3_0_0_1_3_0_0_3
          · exact pair_leaf3_0_0_1_3_0_1
          · exact pair_leaf3_0_0_1_3_0_2
          · exact pair_leaf3_0_0_1_3_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_1_3_1_0
          · exact pair_leaf3_0_0_1_3_1_1
          · exact pair_leaf3_0_0_1_3_1_2
        · exact pair_leaf3_0_0_1_3_2
        · exact pair_leaf3_0_0_1_3_3
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
          · exact pair_leaf3_0_0_1_4_0_0
          · exact pair_leaf3_0_0_1_4_0_1
          · exact pair_leaf3_0_0_1_4_0_2
        · exact pair_leaf3_0_0_1_4_1
        · exact pair_leaf3_0_0_1_4_2
      · exact pair_leaf3_0_0_1_5
      · exact pair_leaf3_0_0_1_6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 5 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_2_0_0_0_0_0
              · exact pair_leaf3_0_0_2_0_0_0_0_1
              · exact pair_leaf3_0_0_2_0_0_0_0_2
              · exact pair_leaf3_0_0_2_0_0_0_0_3
              · exact pair_leaf3_0_0_2_0_0_0_0_4
              · exact pair_leaf3_0_0_2_0_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_2_0_0_0_1_0
              · exact pair_leaf3_0_0_2_0_0_0_1_1
              · exact pair_leaf3_0_0_2_0_0_0_1_2
              · exact pair_leaf3_0_0_2_0_0_0_1_3
              · exact pair_leaf3_0_0_2_0_0_0_1_4
            · exact pair_leaf3_0_0_2_0_0_0_2
            · exact pair_leaf3_0_0_2_0_0_0_3
            · exact pair_leaf3_0_0_2_0_0_0_4
            · exact pair_leaf3_0_0_2_0_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_2_0_0_1_0_0
              · exact pair_leaf3_0_0_2_0_0_1_0_1
              · exact pair_leaf3_0_0_2_0_0_1_0_2
              · exact pair_leaf3_0_0_2_0_0_1_0_3
              · exact pair_leaf3_0_0_2_0_0_1_0_4
              · exact pair_leaf3_0_0_2_0_0_1_0_5
            · exact pair_leaf3_0_0_2_0_0_1_1
            · exact pair_leaf3_0_0_2_0_0_1_2
            · exact pair_leaf3_0_0_2_0_0_1_3
            · exact pair_leaf3_0_0_2_0_0_1_4
            · exact pair_leaf3_0_0_2_0_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_2_0_0_2_0
            · exact pair_leaf3_0_0_2_0_0_2_1
            · exact pair_leaf3_0_0_2_0_0_2_2
            · exact pair_leaf3_0_0_2_0_0_2_3
            · exact pair_leaf3_0_0_2_0_0_2_4
            · exact pair_leaf3_0_0_2_0_0_2_5
          · exact pair_leaf3_0_0_2_0_0_3
          · exact pair_leaf3_0_0_2_0_0_4
          · exact pair_leaf3_0_0_2_0_0_5
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
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_0_2_0_1_0_0_0
              · exact pair_leaf3_0_0_2_0_1_0_0_1
              · exact pair_leaf3_0_0_2_0_1_0_0_2
              · exact pair_leaf3_0_0_2_0_1_0_0_3
              · exact pair_leaf3_0_0_2_0_1_0_0_4
              · exact pair_leaf3_0_0_2_0_1_0_0_5
            · exact pair_leaf3_0_0_2_0_1_0_1
            · exact pair_leaf3_0_0_2_0_1_0_2
            · exact pair_leaf3_0_0_2_0_1_0_3
            · exact pair_leaf3_0_0_2_0_1_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_2_0_1_1_0
            · exact pair_leaf3_0_0_2_0_1_1_1
            · exact pair_leaf3_0_0_2_0_1_1_2
            · exact pair_leaf3_0_0_2_0_1_1_3
            · exact pair_leaf3_0_0_2_0_1_1_4
          · exact pair_leaf3_0_0_2_0_1_2
          · exact pair_leaf3_0_0_2_0_1_3
          · exact pair_leaf3_0_0_2_0_1_4
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
            · exact pair_leaf3_0_0_2_0_2_0_0
            · exact pair_leaf3_0_0_2_0_2_0_1
            · exact pair_leaf3_0_0_2_0_2_0_2
            · exact pair_leaf3_0_0_2_0_2_0_3
          · exact pair_leaf3_0_0_2_0_2_1
          · exact pair_leaf3_0_0_2_0_2_2
          · exact pair_leaf3_0_0_2_0_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_2_0_3_0
          · exact pair_leaf3_0_0_2_0_3_1
          · exact pair_leaf3_0_0_2_0_3_2
        · exact pair_leaf3_0_0_2_0_4
        · exact pair_leaf3_0_0_2_0_5
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
              · exact pair_leaf3_0_0_2_1_0_0_0_0
              · exact pair_leaf3_0_0_2_1_0_0_0_1
              · exact pair_leaf3_0_0_2_1_0_0_0_2
              · exact pair_leaf3_0_0_2_1_0_0_0_3
              · exact pair_leaf3_0_0_2_1_0_0_0_4
            · exact pair_leaf3_0_0_2_1_0_0_1
            · exact pair_leaf3_0_0_2_1_0_0_2
            · exact pair_leaf3_0_0_2_1_0_0_3
            · exact pair_leaf3_0_0_2_1_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_2_1_0_1_0
            · exact pair_leaf3_0_0_2_1_0_1_1
            · exact pair_leaf3_0_0_2_1_0_1_2
            · exact pair_leaf3_0_0_2_1_0_1_3
            · exact pair_leaf3_0_0_2_1_0_1_4
          · exact pair_leaf3_0_0_2_1_0_2
          · exact pair_leaf3_0_0_2_1_0_3
          · exact pair_leaf3_0_0_2_1_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_2_1_1_0_0
            · exact pair_leaf3_0_0_2_1_1_0_1
            · exact pair_leaf3_0_0_2_1_1_0_2
            · exact pair_leaf3_0_0_2_1_1_0_3
            · exact pair_leaf3_0_0_2_1_1_0_4
          · exact pair_leaf3_0_0_2_1_1_1
          · exact pair_leaf3_0_0_2_1_1_2
          · exact pair_leaf3_0_0_2_1_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_2_1_2_0
          · exact pair_leaf3_0_0_2_1_2_1
          · exact pair_leaf3_0_0_2_1_2_2
        · exact pair_leaf3_0_0_2_1_3
        · exact pair_leaf3_0_0_2_1_4
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
            · exact pair_leaf3_0_0_2_2_0_0_0
            · exact pair_leaf3_0_0_2_2_0_0_1
            · exact pair_leaf3_0_0_2_2_0_0_2
            · exact pair_leaf3_0_0_2_2_0_0_3
          · exact pair_leaf3_0_0_2_2_0_1
          · exact pair_leaf3_0_0_2_2_0_2
          · exact pair_leaf3_0_0_2_2_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_2_2_1_0
          · exact pair_leaf3_0_0_2_2_1_1
          · exact pair_leaf3_0_0_2_2_1_2
        · exact pair_leaf3_0_0_2_2_2
        · exact pair_leaf3_0_0_2_2_3
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
          · exact pair_leaf3_0_0_2_3_0_0
          · exact pair_leaf3_0_0_2_3_0_1
          · exact pair_leaf3_0_0_2_3_0_2
        · exact pair_leaf3_0_0_2_3_1
        · exact pair_leaf3_0_0_2_3_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_0_2_4_0
        · exact pair_leaf3_0_0_2_4_1
      · exact pair_leaf3_0_0_2_5
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
              · exact pair_leaf3_0_0_3_0_0_0_0_0
              · exact pair_leaf3_0_0_3_0_0_0_0_1
              · exact pair_leaf3_0_0_3_0_0_0_0_2
              · exact pair_leaf3_0_0_3_0_0_0_0_3
              · exact pair_leaf3_0_0_3_0_0_0_0_4
            · exact pair_leaf3_0_0_3_0_0_0_1
            · exact pair_leaf3_0_0_3_0_0_0_2
            · exact pair_leaf3_0_0_3_0_0_0_3
            · exact pair_leaf3_0_0_3_0_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_0_3_0_0_1_0
            · exact pair_leaf3_0_0_3_0_0_1_1
            · exact pair_leaf3_0_0_3_0_0_1_2
            · exact pair_leaf3_0_0_3_0_0_1_3
            · exact pair_leaf3_0_0_3_0_0_1_4
          · exact pair_leaf3_0_0_3_0_0_2
          · exact pair_leaf3_0_0_3_0_0_3
          · exact pair_leaf3_0_0_3_0_0_4
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
            · exact pair_leaf3_0_0_3_0_1_0_0
            · exact pair_leaf3_0_0_3_0_1_0_1
            · exact pair_leaf3_0_0_3_0_1_0_2
            · exact pair_leaf3_0_0_3_0_1_0_3
          · exact pair_leaf3_0_0_3_0_1_1
          · exact pair_leaf3_0_0_3_0_1_2
          · exact pair_leaf3_0_0_3_0_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_3_0_2_0
          · exact pair_leaf3_0_0_3_0_2_1
          · exact pair_leaf3_0_0_3_0_2_2
        · exact pair_leaf3_0_0_3_0_3
        · exact pair_leaf3_0_0_3_0_4
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
            · exact pair_leaf3_0_0_3_1_0_0_0
            · exact pair_leaf3_0_0_3_1_0_0_1
            · exact pair_leaf3_0_0_3_1_0_0_2
            · exact pair_leaf3_0_0_3_1_0_0_3
          · exact pair_leaf3_0_0_3_1_0_1
          · exact pair_leaf3_0_0_3_1_0_2
          · exact pair_leaf3_0_0_3_1_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_3_1_1_0
          · exact pair_leaf3_0_0_3_1_1_1
          · exact pair_leaf3_0_0_3_1_1_2
        · exact pair_leaf3_0_0_3_1_2
        · exact pair_leaf3_0_0_3_1_3
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
          · exact pair_leaf3_0_0_3_2_0_0
          · exact pair_leaf3_0_0_3_2_0_1
          · exact pair_leaf3_0_0_3_2_0_2
        · exact pair_leaf3_0_0_3_2_1
        · exact pair_leaf3_0_0_3_2_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_0_3_3_0
        · exact pair_leaf3_0_0_3_3_1
      · exact pair_leaf3_0_0_3_4
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
            · exact pair_leaf3_0_0_4_0_0_0_0
            · exact pair_leaf3_0_0_4_0_0_0_1
            · exact pair_leaf3_0_0_4_0_0_0_2
            · exact pair_leaf3_0_0_4_0_0_0_3
          · exact pair_leaf3_0_0_4_0_0_1
          · exact pair_leaf3_0_0_4_0_0_2
          · exact pair_leaf3_0_0_4_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_0_4_0_1_0
          · exact pair_leaf3_0_0_4_0_1_1
          · exact pair_leaf3_0_0_4_0_1_2
        · exact pair_leaf3_0_0_4_0_2
        · exact pair_leaf3_0_0_4_0_3
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
          · exact pair_leaf3_0_0_4_1_0_0
          · exact pair_leaf3_0_0_4_1_0_1
          · exact pair_leaf3_0_0_4_1_0_2
        · exact pair_leaf3_0_0_4_1_1
        · exact pair_leaf3_0_0_4_1_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_0_4_2_0
        · exact pair_leaf3_0_0_4_2_1
      · exact pair_leaf3_0_0_4_3
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
          · exact pair_leaf3_0_0_5_0_0_0
          · exact pair_leaf3_0_0_5_0_0_1
          · exact pair_leaf3_0_0_5_0_0_2
        · exact pair_leaf3_0_0_5_0_1
        · exact pair_leaf3_0_0_5_0_2
      · exact pair_leaf3_0_0_5_1
      · exact pair_leaf3_0_0_5_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_0_0_6_0
      · exact pair_leaf3_0_0_6_1
    · exact pair_leaf3_0_0_7
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 6 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 6 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 6 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 6 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 6 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 6 := by omega
              interval_cases b3
              · apply allLe_intro
                intro a4 ha4
                norm_num at ha4
                have ha4_cases_upper : a4 ≤ 6 := by omega
                interval_cases a4
                · exact pair_leaf3_0_1_0_0_0_0_0_0_0
                · exact pair_leaf3_0_1_0_0_0_0_0_0_1
                · exact pair_leaf3_0_1_0_0_0_0_0_0_2
                · exact pair_leaf3_0_1_0_0_0_0_0_0_3
                · exact pair_leaf3_0_1_0_0_0_0_0_0_4
                · exact pair_leaf3_0_1_0_0_0_0_0_0_5
                · exact pair_leaf3_0_1_0_0_0_0_0_0_6
              · exact pair_leaf3_0_1_0_0_0_0_0_1
              · exact pair_leaf3_0_1_0_0_0_0_0_2
              · exact pair_leaf3_0_1_0_0_0_0_0_3
              · exact pair_leaf3_0_1_0_0_0_0_0_4
              · exact pair_leaf3_0_1_0_0_0_0_0_5
              · exact pair_leaf3_0_1_0_0_0_0_0_6
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_0_0_1_0
              · exact pair_leaf3_0_1_0_0_0_0_1_1
              · exact pair_leaf3_0_1_0_0_0_0_1_2
              · exact pair_leaf3_0_1_0_0_0_0_1_3
              · exact pair_leaf3_0_1_0_0_0_0_1_4
              · exact pair_leaf3_0_1_0_0_0_0_1_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_0_0_2_0
              · exact pair_leaf3_0_1_0_0_0_0_2_1
              · exact pair_leaf3_0_1_0_0_0_0_2_2
              · exact pair_leaf3_0_1_0_0_0_0_2_3
              · exact pair_leaf3_0_1_0_0_0_0_2_4
            · exact pair_leaf3_0_1_0_0_0_0_3
            · exact pair_leaf3_0_1_0_0_0_0_4
            · exact pair_leaf3_0_1_0_0_0_0_5
            · exact pair_leaf3_0_1_0_0_0_0_6
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_0_1_0_0
              · exact pair_leaf3_0_1_0_0_0_1_0_1
              · exact pair_leaf3_0_1_0_0_0_1_0_2
              · exact pair_leaf3_0_1_0_0_0_1_0_3
              · exact pair_leaf3_0_1_0_0_0_1_0_4
              · exact pair_leaf3_0_1_0_0_0_1_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_0_1_1_0
              · exact pair_leaf3_0_1_0_0_0_1_1_1
              · exact pair_leaf3_0_1_0_0_0_1_1_2
              · exact pair_leaf3_0_1_0_0_0_1_1_3
              · exact pair_leaf3_0_1_0_0_0_1_1_4
            · exact pair_leaf3_0_1_0_0_0_1_2
            · exact pair_leaf3_0_1_0_0_0_1_3
            · exact pair_leaf3_0_1_0_0_0_1_4
            · exact pair_leaf3_0_1_0_0_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_0_0_2_0
            · exact pair_leaf3_0_1_0_0_0_2_1
            · exact pair_leaf3_0_1_0_0_0_2_2
            · exact pair_leaf3_0_1_0_0_0_2_3
            · exact pair_leaf3_0_1_0_0_0_2_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_0_0_3_0
            · exact pair_leaf3_0_1_0_0_0_3_1
            · exact pair_leaf3_0_1_0_0_0_3_2
            · exact pair_leaf3_0_1_0_0_0_3_3
          · exact pair_leaf3_0_1_0_0_0_4
          · exact pair_leaf3_0_1_0_0_0_5
          · exact pair_leaf3_0_1_0_0_0_6
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_1_0_0_0
              · exact pair_leaf3_0_1_0_0_1_0_0_1
              · exact pair_leaf3_0_1_0_0_1_0_0_2
              · exact pair_leaf3_0_1_0_0_1_0_0_3
              · exact pair_leaf3_0_1_0_0_1_0_0_4
              · exact pair_leaf3_0_1_0_0_1_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_0_1_0_1_0
              · exact pair_leaf3_0_1_0_0_1_0_1_1
              · exact pair_leaf3_0_1_0_0_1_0_1_2
              · exact pair_leaf3_0_1_0_0_1_0_1_3
              · exact pair_leaf3_0_1_0_0_1_0_1_4
            · exact pair_leaf3_0_1_0_0_1_0_2
            · exact pair_leaf3_0_1_0_0_1_0_3
            · exact pair_leaf3_0_1_0_0_1_0_4
            · exact pair_leaf3_0_1_0_0_1_0_5
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
              · exact pair_leaf3_0_1_0_0_1_1_0_0
              · exact pair_leaf3_0_1_0_0_1_1_0_1
              · exact pair_leaf3_0_1_0_0_1_1_0_2
              · exact pair_leaf3_0_1_0_0_1_1_0_3
              · exact pair_leaf3_0_1_0_0_1_1_0_4
            · exact pair_leaf3_0_1_0_0_1_1_1
            · exact pair_leaf3_0_1_0_0_1_1_2
            · exact pair_leaf3_0_1_0_0_1_1_3
            · exact pair_leaf3_0_1_0_0_1_1_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_0_1_2_0
            · exact pair_leaf3_0_1_0_0_1_2_1
            · exact pair_leaf3_0_1_0_0_1_2_2
            · exact pair_leaf3_0_1_0_0_1_2_3
          · exact pair_leaf3_0_1_0_0_1_3
          · exact pair_leaf3_0_1_0_0_1_4
          · exact pair_leaf3_0_1_0_0_1_5
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
              · exact pair_leaf3_0_1_0_0_2_0_0_0
              · exact pair_leaf3_0_1_0_0_2_0_0_1
              · exact pair_leaf3_0_1_0_0_2_0_0_2
              · exact pair_leaf3_0_1_0_0_2_0_0_3
              · exact pair_leaf3_0_1_0_0_2_0_0_4
            · exact pair_leaf3_0_1_0_0_2_0_1
            · exact pair_leaf3_0_1_0_0_2_0_2
            · exact pair_leaf3_0_1_0_0_2_0_3
            · exact pair_leaf3_0_1_0_0_2_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_0_2_1_0
            · exact pair_leaf3_0_1_0_0_2_1_1
            · exact pair_leaf3_0_1_0_0_2_1_2
            · exact pair_leaf3_0_1_0_0_2_1_3
          · exact pair_leaf3_0_1_0_0_2_2
          · exact pair_leaf3_0_1_0_0_2_3
          · exact pair_leaf3_0_1_0_0_2_4
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
            · exact pair_leaf3_0_1_0_0_3_0_0
            · exact pair_leaf3_0_1_0_0_3_0_1
            · exact pair_leaf3_0_1_0_0_3_0_2
            · exact pair_leaf3_0_1_0_0_3_0_3
          · exact pair_leaf3_0_1_0_0_3_1
          · exact pair_leaf3_0_1_0_0_3_2
          · exact pair_leaf3_0_1_0_0_3_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_0_0_4_0
          · exact pair_leaf3_0_1_0_0_4_1
          · exact pair_leaf3_0_1_0_0_4_2
        · exact pair_leaf3_0_1_0_0_5
        · exact pair_leaf3_0_1_0_0_6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_1_0_0_0_0
              · exact pair_leaf3_0_1_0_1_0_0_0_1
              · exact pair_leaf3_0_1_0_1_0_0_0_2
              · exact pair_leaf3_0_1_0_1_0_0_0_3
              · exact pair_leaf3_0_1_0_1_0_0_0_4
              · exact pair_leaf3_0_1_0_1_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_1_0_0_1_0
              · exact pair_leaf3_0_1_0_1_0_0_1_1
              · exact pair_leaf3_0_1_0_1_0_0_1_2
              · exact pair_leaf3_0_1_0_1_0_0_1_3
              · exact pair_leaf3_0_1_0_1_0_0_1_4
            · exact pair_leaf3_0_1_0_1_0_0_2
            · exact pair_leaf3_0_1_0_1_0_0_3
            · exact pair_leaf3_0_1_0_1_0_0_4
            · exact pair_leaf3_0_1_0_1_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_1_0_1_0
            · exact pair_leaf3_0_1_0_1_0_1_1
            · exact pair_leaf3_0_1_0_1_0_1_2
            · exact pair_leaf3_0_1_0_1_0_1_3
            · exact pair_leaf3_0_1_0_1_0_1_4
            · exact pair_leaf3_0_1_0_1_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_1_0_2_0
            · exact pair_leaf3_0_1_0_1_0_2_1
            · exact pair_leaf3_0_1_0_1_0_2_2
            · exact pair_leaf3_0_1_0_1_0_2_3
            · exact pair_leaf3_0_1_0_1_0_2_4
          · exact pair_leaf3_0_1_0_1_0_3
          · exact pair_leaf3_0_1_0_1_0_4
          · exact pair_leaf3_0_1_0_1_0_5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_0_1_1_0_0_0
              · exact pair_leaf3_0_1_0_1_1_0_0_1
              · exact pair_leaf3_0_1_0_1_1_0_0_2
              · exact pair_leaf3_0_1_0_1_1_0_0_3
              · exact pair_leaf3_0_1_0_1_1_0_0_4
              · exact pair_leaf3_0_1_0_1_1_0_0_5
            · exact pair_leaf3_0_1_0_1_1_0_1
            · exact pair_leaf3_0_1_0_1_1_0_2
            · exact pair_leaf3_0_1_0_1_1_0_3
            · exact pair_leaf3_0_1_0_1_1_0_4
            · exact pair_leaf3_0_1_0_1_1_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_1_1_1_0
            · exact pair_leaf3_0_1_0_1_1_1_1
            · exact pair_leaf3_0_1_0_1_1_1_2
            · exact pair_leaf3_0_1_0_1_1_1_3
            · exact pair_leaf3_0_1_0_1_1_1_4
          · exact pair_leaf3_0_1_0_1_1_2
          · exact pair_leaf3_0_1_0_1_1_3
          · exact pair_leaf3_0_1_0_1_1_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_1_2_0_0
            · exact pair_leaf3_0_1_0_1_2_0_1
            · exact pair_leaf3_0_1_0_1_2_0_2
            · exact pair_leaf3_0_1_0_1_2_0_3
            · exact pair_leaf3_0_1_0_1_2_0_4
          · exact pair_leaf3_0_1_0_1_2_1
          · exact pair_leaf3_0_1_0_1_2_2
          · exact pair_leaf3_0_1_0_1_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_0_1_3_0
          · exact pair_leaf3_0_1_0_1_3_1
          · exact pair_leaf3_0_1_0_1_3_2
        · exact pair_leaf3_0_1_0_1_4
        · exact pair_leaf3_0_1_0_1_5
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
            · exact pair_leaf3_0_1_0_2_0_0_0
            · exact pair_leaf3_0_1_0_2_0_0_1
            · exact pair_leaf3_0_1_0_2_0_0_2
            · exact pair_leaf3_0_1_0_2_0_0_3
            · exact pair_leaf3_0_1_0_2_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_2_0_1_0
            · exact pair_leaf3_0_1_0_2_0_1_1
            · exact pair_leaf3_0_1_0_2_0_1_2
            · exact pair_leaf3_0_1_0_2_0_1_3
            · exact pair_leaf3_0_1_0_2_0_1_4
          · exact pair_leaf3_0_1_0_2_0_2
          · exact pair_leaf3_0_1_0_2_0_3
          · exact pair_leaf3_0_1_0_2_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_0_2_1_0_0
            · exact pair_leaf3_0_1_0_2_1_0_1
            · exact pair_leaf3_0_1_0_2_1_0_2
            · exact pair_leaf3_0_1_0_2_1_0_3
            · exact pair_leaf3_0_1_0_2_1_0_4
          · exact pair_leaf3_0_1_0_2_1_1
          · exact pair_leaf3_0_1_0_2_1_2
          · exact pair_leaf3_0_1_0_2_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_0_2_2_0
          · exact pair_leaf3_0_1_0_2_2_1
          · exact pair_leaf3_0_1_0_2_2_2
        · exact pair_leaf3_0_1_0_2_3
        · exact pair_leaf3_0_1_0_2_4
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
            · exact pair_leaf3_0_1_0_3_0_0_0
            · exact pair_leaf3_0_1_0_3_0_0_1
            · exact pair_leaf3_0_1_0_3_0_0_2
            · exact pair_leaf3_0_1_0_3_0_0_3
          · exact pair_leaf3_0_1_0_3_0_1
          · exact pair_leaf3_0_1_0_3_0_2
          · exact pair_leaf3_0_1_0_3_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_0_3_1_0
          · exact pair_leaf3_0_1_0_3_1_1
          · exact pair_leaf3_0_1_0_3_1_2
        · exact pair_leaf3_0_1_0_3_2
        · exact pair_leaf3_0_1_0_3_3
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · exact pair_leaf3_0_1_0_4_0
        · exact pair_leaf3_0_1_0_4_1
        · exact pair_leaf3_0_1_0_4_2
      · exact pair_leaf3_0_1_0_5
      · exact pair_leaf3_0_1_0_6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 5 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_1_0_0_0_0_0
              · exact pair_leaf3_0_1_1_0_0_0_0_1
              · exact pair_leaf3_0_1_1_0_0_0_0_2
              · exact pair_leaf3_0_1_1_0_0_0_0_3
              · exact pair_leaf3_0_1_1_0_0_0_0_4
              · exact pair_leaf3_0_1_1_0_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_1_0_0_0_1_0
              · exact pair_leaf3_0_1_1_0_0_0_1_1
              · exact pair_leaf3_0_1_1_0_0_0_1_2
              · exact pair_leaf3_0_1_1_0_0_0_1_3
              · exact pair_leaf3_0_1_1_0_0_0_1_4
            · exact pair_leaf3_0_1_1_0_0_0_2
            · exact pair_leaf3_0_1_1_0_0_0_3
            · exact pair_leaf3_0_1_1_0_0_0_4
            · exact pair_leaf3_0_1_1_0_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_1_0_0_1_0_0
              · exact pair_leaf3_0_1_1_0_0_1_0_1
              · exact pair_leaf3_0_1_1_0_0_1_0_2
              · exact pair_leaf3_0_1_1_0_0_1_0_3
              · exact pair_leaf3_0_1_1_0_0_1_0_4
              · exact pair_leaf3_0_1_1_0_0_1_0_5
            · exact pair_leaf3_0_1_1_0_0_1_1
            · exact pair_leaf3_0_1_1_0_0_1_2
            · exact pair_leaf3_0_1_1_0_0_1_3
            · exact pair_leaf3_0_1_1_0_0_1_4
            · exact pair_leaf3_0_1_1_0_0_1_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_1_0_0_2_0
            · exact pair_leaf3_0_1_1_0_0_2_1
            · exact pair_leaf3_0_1_1_0_0_2_2
            · exact pair_leaf3_0_1_1_0_0_2_3
            · exact pair_leaf3_0_1_1_0_0_2_4
          · exact pair_leaf3_0_1_1_0_0_3
          · exact pair_leaf3_0_1_1_0_0_4
          · exact pair_leaf3_0_1_1_0_0_5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 4 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_1_1_0_1_0_0_0
              · exact pair_leaf3_0_1_1_0_1_0_0_1
              · exact pair_leaf3_0_1_1_0_1_0_0_2
              · exact pair_leaf3_0_1_1_0_1_0_0_3
              · exact pair_leaf3_0_1_1_0_1_0_0_4
              · exact pair_leaf3_0_1_1_0_1_0_0_5
            · exact pair_leaf3_0_1_1_0_1_0_1
            · exact pair_leaf3_0_1_1_0_1_0_2
            · exact pair_leaf3_0_1_1_0_1_0_3
            · exact pair_leaf3_0_1_1_0_1_0_4
            · exact pair_leaf3_0_1_1_0_1_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_1_0_1_1_0
            · exact pair_leaf3_0_1_1_0_1_1_1
            · exact pair_leaf3_0_1_1_0_1_1_2
            · exact pair_leaf3_0_1_1_0_1_1_3
            · exact pair_leaf3_0_1_1_0_1_1_4
          · exact pair_leaf3_0_1_1_0_1_2
          · exact pair_leaf3_0_1_1_0_1_3
          · exact pair_leaf3_0_1_1_0_1_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_1_0_2_0_0
            · exact pair_leaf3_0_1_1_0_2_0_1
            · exact pair_leaf3_0_1_1_0_2_0_2
            · exact pair_leaf3_0_1_1_0_2_0_3
            · exact pair_leaf3_0_1_1_0_2_0_4
          · exact pair_leaf3_0_1_1_0_2_1
          · exact pair_leaf3_0_1_1_0_2_2
          · exact pair_leaf3_0_1_1_0_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_1_0_3_0
          · exact pair_leaf3_0_1_1_0_3_1
          · exact pair_leaf3_0_1_1_0_3_2
        · exact pair_leaf3_0_1_1_0_4
        · exact pair_leaf3_0_1_1_0_5
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
              · exact pair_leaf3_0_1_1_1_0_0_0_0
              · exact pair_leaf3_0_1_1_1_0_0_0_1
              · exact pair_leaf3_0_1_1_1_0_0_0_2
              · exact pair_leaf3_0_1_1_1_0_0_0_3
              · exact pair_leaf3_0_1_1_1_0_0_0_4
            · exact pair_leaf3_0_1_1_1_0_0_1
            · exact pair_leaf3_0_1_1_1_0_0_2
            · exact pair_leaf3_0_1_1_1_0_0_3
            · exact pair_leaf3_0_1_1_1_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_1_1_0_1_0
            · exact pair_leaf3_0_1_1_1_0_1_1
            · exact pair_leaf3_0_1_1_1_0_1_2
            · exact pair_leaf3_0_1_1_1_0_1_3
            · exact pair_leaf3_0_1_1_1_0_1_4
          · exact pair_leaf3_0_1_1_1_0_2
          · exact pair_leaf3_0_1_1_1_0_3
          · exact pair_leaf3_0_1_1_1_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_1_1_1_0_0
            · exact pair_leaf3_0_1_1_1_1_0_1
            · exact pair_leaf3_0_1_1_1_1_0_2
            · exact pair_leaf3_0_1_1_1_1_0_3
            · exact pair_leaf3_0_1_1_1_1_0_4
          · exact pair_leaf3_0_1_1_1_1_1
          · exact pair_leaf3_0_1_1_1_1_2
          · exact pair_leaf3_0_1_1_1_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_1_1_2_0
          · exact pair_leaf3_0_1_1_1_2_1
          · exact pair_leaf3_0_1_1_1_2_2
        · exact pair_leaf3_0_1_1_1_3
        · exact pair_leaf3_0_1_1_1_4
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
            · exact pair_leaf3_0_1_1_2_0_0_0
            · exact pair_leaf3_0_1_1_2_0_0_1
            · exact pair_leaf3_0_1_1_2_0_0_2
            · exact pair_leaf3_0_1_1_2_0_0_3
          · exact pair_leaf3_0_1_1_2_0_1
          · exact pair_leaf3_0_1_1_2_0_2
          · exact pair_leaf3_0_1_1_2_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_1_2_1_0
          · exact pair_leaf3_0_1_1_2_1_1
          · exact pair_leaf3_0_1_1_2_1_2
        · exact pair_leaf3_0_1_1_2_2
        · exact pair_leaf3_0_1_1_2_3
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
          · exact pair_leaf3_0_1_1_3_0_0
          · exact pair_leaf3_0_1_1_3_0_1
          · exact pair_leaf3_0_1_1_3_0_2
        · exact pair_leaf3_0_1_1_3_1
        · exact pair_leaf3_0_1_1_3_2
      · exact pair_leaf3_0_1_1_4
      · exact pair_leaf3_0_1_1_5
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
              · exact pair_leaf3_0_1_2_0_0_0_0_0
              · exact pair_leaf3_0_1_2_0_0_0_0_1
              · exact pair_leaf3_0_1_2_0_0_0_0_2
              · exact pair_leaf3_0_1_2_0_0_0_0_3
              · exact pair_leaf3_0_1_2_0_0_0_0_4
            · exact pair_leaf3_0_1_2_0_0_0_1
            · exact pair_leaf3_0_1_2_0_0_0_2
            · exact pair_leaf3_0_1_2_0_0_0_3
            · exact pair_leaf3_0_1_2_0_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_2_0_0_1_0
            · exact pair_leaf3_0_1_2_0_0_1_1
            · exact pair_leaf3_0_1_2_0_0_1_2
            · exact pair_leaf3_0_1_2_0_0_1_3
            · exact pair_leaf3_0_1_2_0_0_1_4
          · exact pair_leaf3_0_1_2_0_0_2
          · exact pair_leaf3_0_1_2_0_0_3
          · exact pair_leaf3_0_1_2_0_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_1_2_0_1_0_0
            · exact pair_leaf3_0_1_2_0_1_0_1
            · exact pair_leaf3_0_1_2_0_1_0_2
            · exact pair_leaf3_0_1_2_0_1_0_3
            · exact pair_leaf3_0_1_2_0_1_0_4
          · exact pair_leaf3_0_1_2_0_1_1
          · exact pair_leaf3_0_1_2_0_1_2
          · exact pair_leaf3_0_1_2_0_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_2_0_2_0
          · exact pair_leaf3_0_1_2_0_2_1
          · exact pair_leaf3_0_1_2_0_2_2
        · exact pair_leaf3_0_1_2_0_3
        · exact pair_leaf3_0_1_2_0_4
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
            · exact pair_leaf3_0_1_2_1_0_0_0
            · exact pair_leaf3_0_1_2_1_0_0_1
            · exact pair_leaf3_0_1_2_1_0_0_2
            · exact pair_leaf3_0_1_2_1_0_0_3
          · exact pair_leaf3_0_1_2_1_0_1
          · exact pair_leaf3_0_1_2_1_0_2
          · exact pair_leaf3_0_1_2_1_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_2_1_1_0
          · exact pair_leaf3_0_1_2_1_1_1
          · exact pair_leaf3_0_1_2_1_1_2
        · exact pair_leaf3_0_1_2_1_2
        · exact pair_leaf3_0_1_2_1_3
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
          · exact pair_leaf3_0_1_2_2_0_0
          · exact pair_leaf3_0_1_2_2_0_1
          · exact pair_leaf3_0_1_2_2_0_2
        · exact pair_leaf3_0_1_2_2_1
        · exact pair_leaf3_0_1_2_2_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_1_2_3_0
        · exact pair_leaf3_0_1_2_3_1
      · exact pair_leaf3_0_1_2_4
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
            · exact pair_leaf3_0_1_3_0_0_0_0
            · exact pair_leaf3_0_1_3_0_0_0_1
            · exact pair_leaf3_0_1_3_0_0_0_2
            · exact pair_leaf3_0_1_3_0_0_0_3
          · exact pair_leaf3_0_1_3_0_0_1
          · exact pair_leaf3_0_1_3_0_0_2
          · exact pair_leaf3_0_1_3_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_1_3_0_1_0
          · exact pair_leaf3_0_1_3_0_1_1
          · exact pair_leaf3_0_1_3_0_1_2
        · exact pair_leaf3_0_1_3_0_2
        · exact pair_leaf3_0_1_3_0_3
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
          · exact pair_leaf3_0_1_3_1_0_0
          · exact pair_leaf3_0_1_3_1_0_1
          · exact pair_leaf3_0_1_3_1_0_2
        · exact pair_leaf3_0_1_3_1_1
        · exact pair_leaf3_0_1_3_1_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_1_3_2_0
        · exact pair_leaf3_0_1_3_2_1
      · exact pair_leaf3_0_1_3_3
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
          · exact pair_leaf3_0_1_4_0_0_0
          · exact pair_leaf3_0_1_4_0_0_1
          · exact pair_leaf3_0_1_4_0_0_2
        · exact pair_leaf3_0_1_4_0_1
        · exact pair_leaf3_0_1_4_0_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_1_4_1_0
        · exact pair_leaf3_0_1_4_1_1
      · exact pair_leaf3_0_1_4_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_0_1_5_0
      · exact pair_leaf3_0_1_5_1
    · exact pair_leaf3_0_1_6
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 5 := by omega
    interval_cases a6
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 5 := by omega
      interval_cases b6
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 5 := by omega
        interval_cases a5
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 5 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 5 := by omega
            interval_cases a3
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 5 := by omega
              interval_cases b3
              · exact pair_leaf3_0_2_0_0_0_0_0_0
              · exact pair_leaf3_0_2_0_0_0_0_0_1
              · exact pair_leaf3_0_2_0_0_0_0_0_2
              · exact pair_leaf3_0_2_0_0_0_0_0_3
              · exact pair_leaf3_0_2_0_0_0_0_0_4
              · exact pair_leaf3_0_2_0_0_0_0_0_5
            · apply allLe_intro
              intro b3 hb3
              norm_num at hb3
              have hb3_cases_upper : b3 ≤ 4 := by omega
              interval_cases b3
              · exact pair_leaf3_0_2_0_0_0_0_1_0
              · exact pair_leaf3_0_2_0_0_0_0_1_1
              · exact pair_leaf3_0_2_0_0_0_0_1_2
              · exact pair_leaf3_0_2_0_0_0_0_1_3
              · exact pair_leaf3_0_2_0_0_0_0_1_4
            · exact pair_leaf3_0_2_0_0_0_0_2
            · exact pair_leaf3_0_2_0_0_0_0_3
            · exact pair_leaf3_0_2_0_0_0_0_4
            · exact pair_leaf3_0_2_0_0_0_0_5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_0_0_0_1_0
            · exact pair_leaf3_0_2_0_0_0_1_1
            · exact pair_leaf3_0_2_0_0_0_1_2
            · exact pair_leaf3_0_2_0_0_0_1_3
            · exact pair_leaf3_0_2_0_0_0_1_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_0_0_0_2_0
            · exact pair_leaf3_0_2_0_0_0_2_1
            · exact pair_leaf3_0_2_0_0_0_2_2
            · exact pair_leaf3_0_2_0_0_0_2_3
          · exact pair_leaf3_0_2_0_0_0_3
          · exact pair_leaf3_0_2_0_0_0_4
          · exact pair_leaf3_0_2_0_0_0_5
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
              · exact pair_leaf3_0_2_0_0_1_0_0_0
              · exact pair_leaf3_0_2_0_0_1_0_0_1
              · exact pair_leaf3_0_2_0_0_1_0_0_2
              · exact pair_leaf3_0_2_0_0_1_0_0_3
              · exact pair_leaf3_0_2_0_0_1_0_0_4
            · exact pair_leaf3_0_2_0_0_1_0_1
            · exact pair_leaf3_0_2_0_0_1_0_2
            · exact pair_leaf3_0_2_0_0_1_0_3
            · exact pair_leaf3_0_2_0_0_1_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_0_0_1_1_0
            · exact pair_leaf3_0_2_0_0_1_1_1
            · exact pair_leaf3_0_2_0_0_1_1_2
            · exact pair_leaf3_0_2_0_0_1_1_3
          · exact pair_leaf3_0_2_0_0_1_2
          · exact pair_leaf3_0_2_0_0_1_3
          · exact pair_leaf3_0_2_0_0_1_4
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
            · exact pair_leaf3_0_2_0_0_2_0_0
            · exact pair_leaf3_0_2_0_0_2_0_1
            · exact pair_leaf3_0_2_0_0_2_0_2
            · exact pair_leaf3_0_2_0_0_2_0_3
          · exact pair_leaf3_0_2_0_0_2_1
          · exact pair_leaf3_0_2_0_0_2_2
          · exact pair_leaf3_0_2_0_0_2_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_0_0_3_0
          · exact pair_leaf3_0_2_0_0_3_1
          · exact pair_leaf3_0_2_0_0_3_2
        · exact pair_leaf3_0_2_0_0_4
        · exact pair_leaf3_0_2_0_0_5
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
            · exact pair_leaf3_0_2_0_1_0_0_0
            · exact pair_leaf3_0_2_0_1_0_0_1
            · exact pair_leaf3_0_2_0_1_0_0_2
            · exact pair_leaf3_0_2_0_1_0_0_3
            · exact pair_leaf3_0_2_0_1_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_0_1_0_1_0
            · exact pair_leaf3_0_2_0_1_0_1_1
            · exact pair_leaf3_0_2_0_1_0_1_2
            · exact pair_leaf3_0_2_0_1_0_1_3
            · exact pair_leaf3_0_2_0_1_0_1_4
          · exact pair_leaf3_0_2_0_1_0_2
          · exact pair_leaf3_0_2_0_1_0_3
          · exact pair_leaf3_0_2_0_1_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_0_1_1_0_0
            · exact pair_leaf3_0_2_0_1_1_0_1
            · exact pair_leaf3_0_2_0_1_1_0_2
            · exact pair_leaf3_0_2_0_1_1_0_3
            · exact pair_leaf3_0_2_0_1_1_0_4
          · exact pair_leaf3_0_2_0_1_1_1
          · exact pair_leaf3_0_2_0_1_1_2
          · exact pair_leaf3_0_2_0_1_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_0_1_2_0
          · exact pair_leaf3_0_2_0_1_2_1
          · exact pair_leaf3_0_2_0_1_2_2
        · exact pair_leaf3_0_2_0_1_3
        · exact pair_leaf3_0_2_0_1_4
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
            · exact pair_leaf3_0_2_0_2_0_0_0
            · exact pair_leaf3_0_2_0_2_0_0_1
            · exact pair_leaf3_0_2_0_2_0_0_2
            · exact pair_leaf3_0_2_0_2_0_0_3
          · exact pair_leaf3_0_2_0_2_0_1
          · exact pair_leaf3_0_2_0_2_0_2
          · exact pair_leaf3_0_2_0_2_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_0_2_1_0
          · exact pair_leaf3_0_2_0_2_1_1
          · exact pair_leaf3_0_2_0_2_1_2
        · exact pair_leaf3_0_2_0_2_2
        · exact pair_leaf3_0_2_0_2_3
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · exact pair_leaf3_0_2_0_3_0
        · exact pair_leaf3_0_2_0_3_1
        · exact pair_leaf3_0_2_0_3_2
      · exact pair_leaf3_0_2_0_4
      · exact pair_leaf3_0_2_0_5
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
              · exact pair_leaf3_0_2_1_0_0_0_0_0
              · exact pair_leaf3_0_2_1_0_0_0_0_1
              · exact pair_leaf3_0_2_1_0_0_0_0_2
              · exact pair_leaf3_0_2_1_0_0_0_0_3
              · exact pair_leaf3_0_2_1_0_0_0_0_4
            · exact pair_leaf3_0_2_1_0_0_0_1
            · exact pair_leaf3_0_2_1_0_0_0_2
            · exact pair_leaf3_0_2_1_0_0_0_3
            · exact pair_leaf3_0_2_1_0_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_1_0_0_1_0
            · exact pair_leaf3_0_2_1_0_0_1_1
            · exact pair_leaf3_0_2_1_0_0_1_2
            · exact pair_leaf3_0_2_1_0_0_1_3
            · exact pair_leaf3_0_2_1_0_0_1_4
          · exact pair_leaf3_0_2_1_0_0_2
          · exact pair_leaf3_0_2_1_0_0_3
          · exact pair_leaf3_0_2_1_0_0_4
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 3 := by omega
          interval_cases b5
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 4 := by omega
            interval_cases a3
            · exact pair_leaf3_0_2_1_0_1_0_0
            · exact pair_leaf3_0_2_1_0_1_0_1
            · exact pair_leaf3_0_2_1_0_1_0_2
            · exact pair_leaf3_0_2_1_0_1_0_3
            · exact pair_leaf3_0_2_1_0_1_0_4
          · exact pair_leaf3_0_2_1_0_1_1
          · exact pair_leaf3_0_2_1_0_1_2
          · exact pair_leaf3_0_2_1_0_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_1_0_2_0
          · exact pair_leaf3_0_2_1_0_2_1
          · exact pair_leaf3_0_2_1_0_2_2
        · exact pair_leaf3_0_2_1_0_3
        · exact pair_leaf3_0_2_1_0_4
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
            · exact pair_leaf3_0_2_1_1_0_0_0
            · exact pair_leaf3_0_2_1_1_0_0_1
            · exact pair_leaf3_0_2_1_1_0_0_2
            · exact pair_leaf3_0_2_1_1_0_0_3
          · exact pair_leaf3_0_2_1_1_0_1
          · exact pair_leaf3_0_2_1_1_0_2
          · exact pair_leaf3_0_2_1_1_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_1_1_1_0
          · exact pair_leaf3_0_2_1_1_1_1
          · exact pair_leaf3_0_2_1_1_1_2
        · exact pair_leaf3_0_2_1_1_2
        · exact pair_leaf3_0_2_1_1_3
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
          · exact pair_leaf3_0_2_1_2_0_0
          · exact pair_leaf3_0_2_1_2_0_1
          · exact pair_leaf3_0_2_1_2_0_2
        · exact pair_leaf3_0_2_1_2_1
        · exact pair_leaf3_0_2_1_2_2
      · exact pair_leaf3_0_2_1_3
      · exact pair_leaf3_0_2_1_4
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
            · exact pair_leaf3_0_2_2_0_0_0_0
            · exact pair_leaf3_0_2_2_0_0_0_1
            · exact pair_leaf3_0_2_2_0_0_0_2
            · exact pair_leaf3_0_2_2_0_0_0_3
          · exact pair_leaf3_0_2_2_0_0_1
          · exact pair_leaf3_0_2_2_0_0_2
          · exact pair_leaf3_0_2_2_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_2_2_0_1_0
          · exact pair_leaf3_0_2_2_0_1_1
          · exact pair_leaf3_0_2_2_0_1_2
        · exact pair_leaf3_0_2_2_0_2
        · exact pair_leaf3_0_2_2_0_3
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
          · exact pair_leaf3_0_2_2_1_0_0
          · exact pair_leaf3_0_2_2_1_0_1
          · exact pair_leaf3_0_2_2_1_0_2
        · exact pair_leaf3_0_2_2_1_1
        · exact pair_leaf3_0_2_2_1_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_2_2_2_0
        · exact pair_leaf3_0_2_2_2_1
      · exact pair_leaf3_0_2_2_3
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
          · exact pair_leaf3_0_2_3_0_0_0
          · exact pair_leaf3_0_2_3_0_0_1
          · exact pair_leaf3_0_2_3_0_0_2
        · exact pair_leaf3_0_2_3_0_1
        · exact pair_leaf3_0_2_3_0_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_2_3_1_0
        · exact pair_leaf3_0_2_3_1_1
      · exact pair_leaf3_0_2_3_2
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
        · exact pair_leaf3_0_2_4_0_0
        · exact pair_leaf3_0_2_4_0_1
      · exact pair_leaf3_0_2_4_1
    · exact pair_leaf3_0_2_5
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
            · exact pair_leaf3_0_3_0_0_0_0_0
            · exact pair_leaf3_0_3_0_0_0_0_1
            · exact pair_leaf3_0_3_0_0_0_0_2
            · exact pair_leaf3_0_3_0_0_0_0_3
            · exact pair_leaf3_0_3_0_0_0_0_4
          · apply allLe_intro
            intro a3 ha3
            norm_num at ha3
            have ha3_cases_upper : a3 ≤ 3 := by omega
            interval_cases a3
            · exact pair_leaf3_0_3_0_0_0_1_0
            · exact pair_leaf3_0_3_0_0_0_1_1
            · exact pair_leaf3_0_3_0_0_0_1_2
            · exact pair_leaf3_0_3_0_0_0_1_3
          · exact pair_leaf3_0_3_0_0_0_2
          · exact pair_leaf3_0_3_0_0_0_3
          · exact pair_leaf3_0_3_0_0_0_4
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
            · exact pair_leaf3_0_3_0_0_1_0_0
            · exact pair_leaf3_0_3_0_0_1_0_1
            · exact pair_leaf3_0_3_0_0_1_0_2
            · exact pair_leaf3_0_3_0_0_1_0_3
          · exact pair_leaf3_0_3_0_0_1_1
          · exact pair_leaf3_0_3_0_0_1_2
          · exact pair_leaf3_0_3_0_0_1_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_3_0_0_2_0
          · exact pair_leaf3_0_3_0_0_2_1
          · exact pair_leaf3_0_3_0_0_2_2
        · exact pair_leaf3_0_3_0_0_3
        · exact pair_leaf3_0_3_0_0_4
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
            · exact pair_leaf3_0_3_0_1_0_0_0
            · exact pair_leaf3_0_3_0_1_0_0_1
            · exact pair_leaf3_0_3_0_1_0_0_2
            · exact pair_leaf3_0_3_0_1_0_0_3
          · exact pair_leaf3_0_3_0_1_0_1
          · exact pair_leaf3_0_3_0_1_0_2
          · exact pair_leaf3_0_3_0_1_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_3_0_1_1_0
          · exact pair_leaf3_0_3_0_1_1_1
          · exact pair_leaf3_0_3_0_1_1_2
        · exact pair_leaf3_0_3_0_1_2
        · exact pair_leaf3_0_3_0_1_3
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · exact pair_leaf3_0_3_0_2_0
        · exact pair_leaf3_0_3_0_2_1
        · exact pair_leaf3_0_3_0_2_2
      · exact pair_leaf3_0_3_0_3
      · exact pair_leaf3_0_3_0_4
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
            · exact pair_leaf3_0_3_1_0_0_0_0
            · exact pair_leaf3_0_3_1_0_0_0_1
            · exact pair_leaf3_0_3_1_0_0_0_2
            · exact pair_leaf3_0_3_1_0_0_0_3
          · exact pair_leaf3_0_3_1_0_0_1
          · exact pair_leaf3_0_3_1_0_0_2
          · exact pair_leaf3_0_3_1_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_3_1_0_1_0
          · exact pair_leaf3_0_3_1_0_1_1
          · exact pair_leaf3_0_3_1_0_1_2
        · exact pair_leaf3_0_3_1_0_2
        · exact pair_leaf3_0_3_1_0_3
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
          · exact pair_leaf3_0_3_1_1_0_0
          · exact pair_leaf3_0_3_1_1_0_1
          · exact pair_leaf3_0_3_1_1_0_2
        · exact pair_leaf3_0_3_1_1_1
        · exact pair_leaf3_0_3_1_1_2
      · exact pair_leaf3_0_3_1_2
      · exact pair_leaf3_0_3_1_3
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
          · exact pair_leaf3_0_3_2_0_0_0
          · exact pair_leaf3_0_3_2_0_0_1
          · exact pair_leaf3_0_3_2_0_0_2
        · exact pair_leaf3_0_3_2_0_1
        · exact pair_leaf3_0_3_2_0_2
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 1 := by omega
        interval_cases a5
        · exact pair_leaf3_0_3_2_1_0
        · exact pair_leaf3_0_3_2_1_1
      · exact pair_leaf3_0_3_2_2
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
        · exact pair_leaf3_0_3_3_0_0
        · exact pair_leaf3_0_3_3_0_1
      · exact pair_leaf3_0_3_3_1
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 0 := by omega
      interval_cases b6
      · exact pair_leaf3_0_3_4_0
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
            · exact pair_leaf3_0_4_0_0_0_0_0
            · exact pair_leaf3_0_4_0_0_0_0_1
            · exact pair_leaf3_0_4_0_0_0_0_2
            · exact pair_leaf3_0_4_0_0_0_0_3
          · exact pair_leaf3_0_4_0_0_0_1
          · exact pair_leaf3_0_4_0_0_0_2
          · exact pair_leaf3_0_4_0_0_0_3
        · apply allLe_intro
          intro b5 hb5
          norm_num at hb5
          have hb5_cases_upper : b5 ≤ 2 := by omega
          interval_cases b5
          · exact pair_leaf3_0_4_0_0_1_0
          · exact pair_leaf3_0_4_0_0_1_1
          · exact pair_leaf3_0_4_0_0_1_2
        · exact pair_leaf3_0_4_0_0_2
        · exact pair_leaf3_0_4_0_0_3
      · apply allLe_intro
        intro a5 ha5
        norm_num at ha5
        have ha5_cases_upper : a5 ≤ 2 := by omega
        interval_cases a5
        · exact pair_leaf3_0_4_0_1_0
        · exact pair_leaf3_0_4_0_1_1
        · exact pair_leaf3_0_4_0_1_2
      · exact pair_leaf3_0_4_0_2
      · exact pair_leaf3_0_4_0_3
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
          · exact pair_leaf3_0_4_1_0_0_0
          · exact pair_leaf3_0_4_1_0_0_1
          · exact pair_leaf3_0_4_1_0_0_2
        · exact pair_leaf3_0_4_1_0_1
        · exact pair_leaf3_0_4_1_0_2
      · exact pair_leaf3_0_4_1_1
      · exact pair_leaf3_0_4_1_2
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
        · exact pair_leaf3_0_4_2_0_0
        · exact pair_leaf3_0_4_2_0_1
      · exact pair_leaf3_0_4_2_1
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 0 := by omega
      interval_cases b6
      · exact pair_leaf3_0_4_3_0
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
        · exact pair_leaf3_0_5_0_0_0
        · exact pair_leaf3_0_5_0_0_1
        · exact pair_leaf3_0_5_0_0_2
      · exact pair_leaf3_0_5_0_1
      · exact pair_leaf3_0_5_0_2
    · apply allLe_intro
      intro b6 hb6
      norm_num at hb6
      have hb6_cases_upper : b6 ≤ 1 := by omega
      interval_cases b6
      · exact pair_leaf3_0_5_1_0
      · exact pair_leaf3_0_5_1_1
    · exact pair_leaf3_0_5_2
  · apply allLe_intro
    intro a6 ha6
    norm_num at ha6
    have ha6_cases_upper : a6 ≤ 1 := by omega
    interval_cases a6
    · exact pair_leaf3_0_6_0
    · exact pair_leaf3_0_6_1
  · exact pair_leaf3_0_7

end Paper6FiveExclusion

#print axioms Paper6FiveExclusion.assembled_pair3_0
