import Research.Backfill.Paper6.LiteralCertificates3_00
import Research.Backfill.Paper6.LiteralCertificates3_01
import Research.Backfill.Paper6.LiteralCertificates3_02
import Research.Backfill.Paper6.LiteralCertificates4_00
import Research.Backfill.Paper6.LiteralCertificates4_01
import Research.Backfill.Paper6.LiteralCertificates4_02
import Research.Backfill.Paper6.LiteralCertificates4_03
import Research.Backfill.Paper6.LiteralCertificates4_04
import Research.Backfill.Paper6.LiteralCertificates4_05
import Research.Backfill.Paper6.LiteralCertificates4_06
import Research.Backfill.Paper6.LiteralCertificates4_07
import Research.Backfill.Paper6.LiteralCertificates4_08
import Research.Backfill.Paper6.LiteralCertificates4_09
import Research.Backfill.Paper6.LiteralCertificates4_10
import Research.Backfill.Paper6.LiteralCertificates4_11
import Research.Backfill.Paper6.LiteralCertificates4_12
import Research.Backfill.Paper6.LiteralCertificates4_13
import Research.Backfill.Paper6.LiteralCertificates4_14
import Research.Backfill.Paper6.LiteralCertificates4_15
import Research.Backfill.Paper6.LiteralCertificates4_16
import Research.Backfill.Paper6.LiteralCertificates4_17
import Research.Backfill.Paper6.LiteralCertificates4_18
import Research.Backfill.Paper6.LiteralCertificates4_19
import Research.Backfill.Paper6.LiteralCertificates4_20
import Research.Backfill.Paper6.LiteralCertificates4_21
import Research.Backfill.Paper6.LiteralCertificates4_22
import Research.Backfill.Paper6.LiteralCertificates4_23
import Research.Backfill.Paper6.LiteralCertificates4_24
import Research.Backfill.Paper6.LiteralCertificates4_25
import Research.Backfill.Paper6.LiteralCertificates4_26
import Research.Backfill.Paper6.LiteralCertificates4_27
import Research.Backfill.Paper6.LiteralCertificates4_28
import Research.Backfill.Paper6.LiteralCertificates4_29
import Research.Backfill.Paper6.LiteralCertificates4_30
import Research.Backfill.Paper6.LiteralCertificates4_31
import Research.Backfill.Paper6.LiteralCertificates4_32
import Research.Backfill.Paper6.LiteralCertificates4_33
import Research.Backfill.Paper6.LiteralCertificates4_34
import Research.Backfill.Paper6.LiteralCertificates4_35
import Research.Backfill.Paper6.LiteralCertificates4_36
import Research.Backfill.Paper6.LiteralCertificates4_37
import Research.Backfill.Paper6.LiteralCertificates4_38
import Research.Backfill.Paper6.LiteralCertificates4_39
import Research.Backfill.Paper6.LiteralCertificates4_40
import Research.Backfill.Paper6.LiteralCertificates4_41
import Research.Backfill.Paper6.LiteralCertificates4_42
import Research.Backfill.Paper6.LiteralCertificates4_43
import Research.Backfill.Paper6.LiteralCertificates4_44
import Research.Backfill.Paper6.LiteralCertificates4_45
import Research.Backfill.Paper6.LiteralCertificates4_46
import Research.Backfill.Paper6.LiteralCertificates4_47
import Research.Backfill.Paper6.LiteralCertificates4_48
import Research.Backfill.Paper6.LiteralCertificates4_49

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

set_option maxHeartbeats 400000 in
theorem all_counts3 : checkCounts3 = true := by
  unfold checkCounts3
  apply allLe_intro
  intro r7 hr7
  norm_num at hr7
  have hr7_cases_upper : r7 ≤ 6 := by omega
  interval_cases r7
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 6 := by omega
    interval_cases r6
    · exact certificate3_0_0
    · exact certificate3_0_1
    · exact certificate3_0_2
    · exact certificate3_0_3
    · exact certificate3_0_4
    · exact certificate3_0_5
    · exact certificate3_0_6
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 5 := by omega
    interval_cases r6
    · exact certificate3_1_0
    · exact certificate3_1_1
    · exact certificate3_1_2
    · exact certificate3_1_3
    · exact certificate3_1_4
    · exact certificate3_1_5
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 4 := by omega
    interval_cases r6
    · exact certificate3_2_0
    · exact certificate3_2_1
    · exact certificate3_2_2
    · exact certificate3_2_3
    · exact certificate3_2_4
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 3 := by omega
    interval_cases r6
    · exact certificate3_3_0
    · exact certificate3_3_1
    · exact certificate3_3_2
    · exact certificate3_3_3
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 2 := by omega
    interval_cases r6
    · exact certificate3_4_0
    · exact certificate3_4_1
    · exact certificate3_4_2
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 1 := by omega
    interval_cases r6
    · exact certificate3_5_0
    · exact certificate3_5_1
  · apply allLe_intro
    intro r6 hr6
    norm_num at hr6
    have hr6_cases_upper : r6 ≤ 0 := by omega
    interval_cases r6
    · exact certificate3_6_0

set_option maxHeartbeats 400000 in
theorem all_counts4 : checkCounts4 = true := by
  unfold checkCounts4
  apply allLe_intro
  intro r15 hr15
  norm_num at hr15
  have hr15_cases_upper : r15 ≤ 6 := by omega
  interval_cases r15
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 6 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 6 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 6 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 6 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_0_0
          · exact certificate4_0_0_0_0_1
          · exact certificate4_0_0_0_0_2
          · exact certificate4_0_0_0_0_3
          · exact certificate4_0_0_0_0_4
          · exact certificate4_0_0_0_0_5
          · exact certificate4_0_0_0_0_6
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 5 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_1_0
          · exact certificate4_0_0_0_1_1
          · exact certificate4_0_0_0_1_2
          · exact certificate4_0_0_0_1_3
          · exact certificate4_0_0_0_1_4
          · exact certificate4_0_0_0_1_5
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_2_0
          · exact certificate4_0_0_0_2_1
          · exact certificate4_0_0_0_2_2
          · exact certificate4_0_0_0_2_3
          · exact certificate4_0_0_0_2_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_3_0
          · exact certificate4_0_0_0_3_1
          · exact certificate4_0_0_0_3_2
          · exact certificate4_0_0_0_3_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_4_0
          · exact certificate4_0_0_0_4_1
          · exact certificate4_0_0_0_4_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_5_0
          · exact certificate4_0_0_0_5_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_0_6_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 5 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 5 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_0_0
          · exact certificate4_0_0_1_0_1
          · exact certificate4_0_0_1_0_2
          · exact certificate4_0_0_1_0_3
          · exact certificate4_0_0_1_0_4
          · exact certificate4_0_0_1_0_5
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_1_0
          · exact certificate4_0_0_1_1_1
          · exact certificate4_0_0_1_1_2
          · exact certificate4_0_0_1_1_3
          · exact certificate4_0_0_1_1_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_2_0
          · exact certificate4_0_0_1_2_1
          · exact certificate4_0_0_1_2_2
          · exact certificate4_0_0_1_2_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_3_0
          · exact certificate4_0_0_1_3_1
          · exact certificate4_0_0_1_3_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_4_0
          · exact certificate4_0_0_1_4_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_1_5_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_0_2_0_0
          · exact certificate4_0_0_2_0_1
          · exact certificate4_0_0_2_0_2
          · exact certificate4_0_0_2_0_3
          · exact certificate4_0_0_2_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_0_2_1_0
          · exact certificate4_0_0_2_1_1
          · exact certificate4_0_0_2_1_2
          · exact certificate4_0_0_2_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_0_2_2_0
          · exact certificate4_0_0_2_2_1
          · exact certificate4_0_0_2_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_2_3_0
          · exact certificate4_0_0_2_3_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_2_4_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_0_3_0_0
          · exact certificate4_0_0_3_0_1
          · exact certificate4_0_0_3_0_2
          · exact certificate4_0_0_3_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_0_3_1_0
          · exact certificate4_0_0_3_1_1
          · exact certificate4_0_0_3_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_3_2_0
          · exact certificate4_0_0_3_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_3_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_0_4_0_0
          · exact certificate4_0_0_4_0_1
          · exact certificate4_0_0_4_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_4_1_0
          · exact certificate4_0_0_4_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_4_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_0_5_0_0
          · exact certificate4_0_0_5_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_5_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_0_6_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 5 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 5 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 5 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_0_0
          · exact certificate4_0_1_0_0_1
          · exact certificate4_0_1_0_0_2
          · exact certificate4_0_1_0_0_3
          · exact certificate4_0_1_0_0_4
          · exact certificate4_0_1_0_0_5
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_1_0
          · exact certificate4_0_1_0_1_1
          · exact certificate4_0_1_0_1_2
          · exact certificate4_0_1_0_1_3
          · exact certificate4_0_1_0_1_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_2_0
          · exact certificate4_0_1_0_2_1
          · exact certificate4_0_1_0_2_2
          · exact certificate4_0_1_0_2_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_3_0
          · exact certificate4_0_1_0_3_1
          · exact certificate4_0_1_0_3_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_4_0
          · exact certificate4_0_1_0_4_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_1_0_5_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_1_1_0_0
          · exact certificate4_0_1_1_0_1
          · exact certificate4_0_1_1_0_2
          · exact certificate4_0_1_1_0_3
          · exact certificate4_0_1_1_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_1_1_1_0
          · exact certificate4_0_1_1_1_1
          · exact certificate4_0_1_1_1_2
          · exact certificate4_0_1_1_1_3
          · exact certificate4_0_1_1_1_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_1_1_2_0
          · exact certificate4_0_1_1_2_1
          · exact certificate4_0_1_1_2_2
          · exact certificate4_0_1_1_2_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_1_1_3_0
          · exact certificate4_0_1_1_3_1
          · exact certificate4_0_1_1_3_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_1_4_0
          · exact certificate4_0_1_1_4_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_1_2_0_0
          · exact certificate4_0_1_2_0_1
          · exact certificate4_0_1_2_0_2
          · exact certificate4_0_1_2_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_1_2_1_0
          · exact certificate4_0_1_2_1_1
          · exact certificate4_0_1_2_1_2
          · exact certificate4_0_1_2_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_1_2_2_0
          · exact certificate4_0_1_2_2_1
          · exact certificate4_0_1_2_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_2_3_0
          · exact certificate4_0_1_2_3_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_1_3_0_0
          · exact certificate4_0_1_3_0_1
          · exact certificate4_0_1_3_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_1_3_1_0
          · exact certificate4_0_1_3_1_1
          · exact certificate4_0_1_3_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_3_2_0
          · exact certificate4_0_1_3_2_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_4_0_0
          · exact certificate4_0_1_4_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_1_4_1_0
          · exact certificate4_0_1_4_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_1_5_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 4 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_0_2_0_0_0
          · exact certificate4_0_2_0_0_1
          · exact certificate4_0_2_0_0_2
          · exact certificate4_0_2_0_0_3
          · exact certificate4_0_2_0_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_2_0_1_0
          · exact certificate4_0_2_0_1_1
          · exact certificate4_0_2_0_1_2
          · exact certificate4_0_2_0_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_2_0_2_0
          · exact certificate4_0_2_0_2_1
          · exact certificate4_0_2_0_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_2_0_3_0
          · exact certificate4_0_2_0_3_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_2_0_4_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_2_1_0_0
          · exact certificate4_0_2_1_0_1
          · exact certificate4_0_2_1_0_2
          · exact certificate4_0_2_1_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_2_1_1_0
          · exact certificate4_0_2_1_1_1
          · exact certificate4_0_2_1_1_2
          · exact certificate4_0_2_1_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_2_1_2_0
          · exact certificate4_0_2_1_2_1
          · exact certificate4_0_2_1_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_2_1_3_0
          · exact certificate4_0_2_1_3_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_2_2_0_0
          · exact certificate4_0_2_2_0_1
          · exact certificate4_0_2_2_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_2_2_1_0
          · exact certificate4_0_2_2_1_1
          · exact certificate4_0_2_2_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_2_2_2_0
          · exact certificate4_0_2_2_2_1
          · exact certificate4_0_2_2_2_2
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_2_3_0_0
          · exact certificate4_0_2_3_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_2_3_1_0
          · exact certificate4_0_2_3_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_2_4_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 3 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_0_3_0_0_0
          · exact certificate4_0_3_0_0_1
          · exact certificate4_0_3_0_0_2
          · exact certificate4_0_3_0_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_3_0_1_0
          · exact certificate4_0_3_0_1_1
          · exact certificate4_0_3_0_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_3_0_2_0
          · exact certificate4_0_3_0_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_3_0_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_3_1_0_0
          · exact certificate4_0_3_1_0_1
          · exact certificate4_0_3_1_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_3_1_1_0
          · exact certificate4_0_3_1_1_1
          · exact certificate4_0_3_1_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_3_1_2_0
          · exact certificate4_0_3_1_2_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_3_2_0_0
          · exact certificate4_0_3_2_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_3_2_1_0
          · exact certificate4_0_3_2_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_3_3_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 2 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_0_4_0_0_0
          · exact certificate4_0_4_0_0_1
          · exact certificate4_0_4_0_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_4_0_1_0
          · exact certificate4_0_4_0_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_4_0_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_4_1_0_0
          · exact certificate4_0_4_1_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_4_1_1_0
          · exact certificate4_0_4_1_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_4_2_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_0_5_0_0_0
          · exact certificate4_0_5_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_5_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_5_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_0_6_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 5 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 5 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 5 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 5 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_0_0
          · exact certificate4_1_0_0_0_1
          · exact certificate4_1_0_0_0_2
          · exact certificate4_1_0_0_0_3
          · exact certificate4_1_0_0_0_4
          · exact certificate4_1_0_0_0_5
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_1_0
          · exact certificate4_1_0_0_1_1
          · exact certificate4_1_0_0_1_2
          · exact certificate4_1_0_0_1_3
          · exact certificate4_1_0_0_1_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_2_0
          · exact certificate4_1_0_0_2_1
          · exact certificate4_1_0_0_2_2
          · exact certificate4_1_0_0_2_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_3_0
          · exact certificate4_1_0_0_3_1
          · exact certificate4_1_0_0_3_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_4_0
          · exact certificate4_1_0_0_4_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_0_5_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_1_0_1_0_0
          · exact certificate4_1_0_1_0_1
          · exact certificate4_1_0_1_0_2
          · exact certificate4_1_0_1_0_3
          · exact certificate4_1_0_1_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_0_1_1_0
          · exact certificate4_1_0_1_1_1
          · exact certificate4_1_0_1_1_2
          · exact certificate4_1_0_1_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_0_1_2_0
          · exact certificate4_1_0_1_2_1
          · exact certificate4_1_0_1_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_0_1_3_0
          · exact certificate4_1_0_1_3_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_1_4_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_0_2_0_0
          · exact certificate4_1_0_2_0_1
          · exact certificate4_1_0_2_0_2
          · exact certificate4_1_0_2_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_0_2_1_0
          · exact certificate4_1_0_2_1_1
          · exact certificate4_1_0_2_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_0_2_2_0
          · exact certificate4_1_0_2_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_2_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_0_3_0_0
          · exact certificate4_1_0_3_0_1
          · exact certificate4_1_0_3_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_0_3_1_0
          · exact certificate4_1_0_3_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_3_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_0_4_0_0
          · exact certificate4_1_0_4_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_4_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_0_5_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 4 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_1_1_0_0_0
          · exact certificate4_1_1_0_0_1
          · exact certificate4_1_1_0_0_2
          · exact certificate4_1_1_0_0_3
          · exact certificate4_1_1_0_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_1_0_1_0
          · exact certificate4_1_1_0_1_1
          · exact certificate4_1_1_0_1_2
          · exact certificate4_1_1_0_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_1_0_2_0
          · exact certificate4_1_1_0_2_1
          · exact certificate4_1_1_0_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_1_0_3_0
          · exact certificate4_1_1_0_3_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_1_0_4_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_1_1_0_0
          · exact certificate4_1_1_1_0_1
          · exact certificate4_1_1_1_0_2
          · exact certificate4_1_1_1_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_1_1_1_0
          · exact certificate4_1_1_1_1_1
          · exact certificate4_1_1_1_1_2
          · exact certificate4_1_1_1_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_1_1_2_0
          · exact certificate4_1_1_1_2_1
          · exact certificate4_1_1_1_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_1_1_3_0
          · exact certificate4_1_1_1_3_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_1_2_0_0
          · exact certificate4_1_1_2_0_1
          · exact certificate4_1_1_2_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_1_2_1_0
          · exact certificate4_1_1_2_1_1
          · exact certificate4_1_1_2_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_1_2_2_0
          · exact certificate4_1_1_2_2_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_1_3_0_0
          · exact certificate4_1_1_3_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_1_3_1_0
          · exact certificate4_1_1_3_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_1_4_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 3 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_1_2_0_0_0
          · exact certificate4_1_2_0_0_1
          · exact certificate4_1_2_0_0_2
          · exact certificate4_1_2_0_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_2_0_1_0
          · exact certificate4_1_2_0_1_1
          · exact certificate4_1_2_0_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_2_0_2_0
          · exact certificate4_1_2_0_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_2_0_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_2_1_0_0
          · exact certificate4_1_2_1_0_1
          · exact certificate4_1_2_1_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_2_1_1_0
          · exact certificate4_1_2_1_1_1
          · exact certificate4_1_2_1_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_2_1_2_0
          · exact certificate4_1_2_1_2_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_2_2_0_0
          · exact certificate4_1_2_2_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_2_2_1_0
          · exact certificate4_1_2_2_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_2_3_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 2 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_1_3_0_0_0
          · exact certificate4_1_3_0_0_1
          · exact certificate4_1_3_0_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_3_0_1_0
          · exact certificate4_1_3_0_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_3_0_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_3_1_0_0
          · exact certificate4_1_3_1_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_3_1_1_0
          · exact certificate4_1_3_1_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_3_2_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_1_4_0_0_0
          · exact certificate4_1_4_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_4_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_4_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_1_5_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 4 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 4 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 4 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 4 := by omega
          interval_cases r7
          · exact certificate4_2_0_0_0_0
          · exact certificate4_2_0_0_0_1
          · exact certificate4_2_0_0_0_2
          · exact certificate4_2_0_0_0_3
          · exact certificate4_2_0_0_0_4
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_2_0_0_1_0
          · exact certificate4_2_0_0_1_1
          · exact certificate4_2_0_0_1_2
          · exact certificate4_2_0_0_1_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_0_0_2_0
          · exact certificate4_2_0_0_2_1
          · exact certificate4_2_0_0_2_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_0_0_3_0
          · exact certificate4_2_0_0_3_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_0_0_4_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_2_0_1_0_0
          · exact certificate4_2_0_1_0_1
          · exact certificate4_2_0_1_0_2
          · exact certificate4_2_0_1_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_0_1_1_0
          · exact certificate4_2_0_1_1_1
          · exact certificate4_2_0_1_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_0_1_2_0
          · exact certificate4_2_0_1_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_0_1_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_0_2_0_0
          · exact certificate4_2_0_2_0_1
          · exact certificate4_2_0_2_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_0_2_1_0
          · exact certificate4_2_0_2_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_0_2_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_0_3_0_0
          · exact certificate4_2_0_3_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_0_3_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_0_4_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 3 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_2_1_0_0_0
          · exact certificate4_2_1_0_0_1
          · exact certificate4_2_1_0_0_2
          · exact certificate4_2_1_0_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_1_0_1_0
          · exact certificate4_2_1_0_1_1
          · exact certificate4_2_1_0_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_1_0_2_0
          · exact certificate4_2_1_0_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_1_0_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_1_1_0_0
          · exact certificate4_2_1_1_0_1
          · exact certificate4_2_1_1_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_1_1_1_0
          · exact certificate4_2_1_1_1_1
          · exact certificate4_2_1_1_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_1_1_2_0
          · exact certificate4_2_1_1_2_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_1_2_0_0
          · exact certificate4_2_1_2_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_1_2_1_0
          · exact certificate4_2_1_2_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_1_3_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 2 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_2_2_0_0_0
          · exact certificate4_2_2_0_0_1
          · exact certificate4_2_2_0_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_2_0_1_0
          · exact certificate4_2_2_0_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_2_0_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_2_1_0_0
          · exact certificate4_2_2_1_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_2_1_1_0
          · exact certificate4_2_2_1_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_2_2_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_2_3_0_0_0
          · exact certificate4_2_3_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_3_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_3_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_2_4_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 3 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 3 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 3 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 3 := by omega
          interval_cases r7
          · exact certificate4_3_0_0_0_0
          · exact certificate4_3_0_0_0_1
          · exact certificate4_3_0_0_0_2
          · exact certificate4_3_0_0_0_3
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_3_0_0_1_0
          · exact certificate4_3_0_0_1_1
          · exact certificate4_3_0_0_1_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_0_0_2_0
          · exact certificate4_3_0_0_2_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_0_0_3_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_3_0_1_0_0
          · exact certificate4_3_0_1_0_1
          · exact certificate4_3_0_1_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_0_1_1_0
          · exact certificate4_3_0_1_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_0_1_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_0_2_0_0
          · exact certificate4_3_0_2_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_0_2_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_0_3_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 2 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_3_1_0_0_0
          · exact certificate4_3_1_0_0_1
          · exact certificate4_3_1_0_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_1_0_1_0
          · exact certificate4_3_1_0_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_1_0_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_1_1_0_0
          · exact certificate4_3_1_1_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_1_1_1_0
          · exact certificate4_3_1_1_1_1
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_1_2_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_3_2_0_0_0
          · exact certificate4_3_2_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_2_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_2_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_3_3_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 2 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 2 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 2 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 2 := by omega
          interval_cases r7
          · exact certificate4_4_0_0_0_0
          · exact certificate4_4_0_0_0_1
          · exact certificate4_4_0_0_0_2
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_4_0_0_1_0
          · exact certificate4_4_0_0_1_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_0_0_2_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_4_0_1_0_0
          · exact certificate4_4_0_1_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_0_1_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_0_2_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_4_1_0_0_0
          · exact certificate4_4_1_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_1_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_1_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_4_2_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 1 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 1 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 1 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 1 := by omega
          interval_cases r7
          · exact certificate4_5_0_0_0_0
          · exact certificate4_5_0_0_0_1
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_5_0_0_1_0
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_5_0_1_0_0
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_5_1_0_0_0
  · apply allLe_intro
    intro r14 hr14
    norm_num at hr14
    have hr14_cases_upper : r14 ≤ 0 := by omega
    interval_cases r14
    · apply allLe_intro
      intro r13 hr13
      norm_num at hr13
      have hr13_cases_upper : r13 ≤ 0 := by omega
      interval_cases r13
      · apply allLe_intro
        intro r11 hr11
        norm_num at hr11
        have hr11_cases_upper : r11 ≤ 0 := by omega
        interval_cases r11
        · apply allLe_intro
          intro r7 hr7
          norm_num at hr7
          have hr7_cases_upper : r7 ≤ 0 := by omega
          interval_cases r7
          · exact certificate4_6_0_0_0_0

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.all_counts3
#print axioms Paper6LiteralLouWang.all_counts4
