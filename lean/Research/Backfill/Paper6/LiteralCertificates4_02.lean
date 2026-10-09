import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_14
import Research.Backfill.Paper6.LiteralLeaves4_15
import Research.Backfill.Paper6.LiteralLeaves4_16
import Research.Backfill.Paper6.LiteralLeaves4_17

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [1, 1, 4, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_3_2 : suffix4 0 0 0 3 2 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_3_2_0_0
    · exact leaf4_0_0_0_3_2_0_1
  · exact leaf4_0_0_0_3_2_1
  · exact leaf4_0_0_0_3_2_2
  · exact leaf4_0_0_0_3_2_3

-- Residual total budget 6; residual column budgets [0, 0, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_3_3 : suffix4 0 0 0 3 3 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [2, 2, 6, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_4_0 : suffix4 0 0 0 4 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_4_0_0_0_0
      · exact leaf4_0_0_0_4_0_0_0_1
      · exact leaf4_0_0_0_4_0_0_0_2
    · exact leaf4_0_0_0_4_0_0_1
    · exact leaf4_0_0_0_4_0_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_4_0_1_0
    · exact leaf4_0_0_0_4_0_1_1
  · exact leaf4_0_0_0_4_0_2

-- Residual total budget 7; residual column budgets [1, 1, 5, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_4_1 : suffix4 0 0 0 4 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_4_1_0_0
    · exact leaf4_0_0_0_4_1_0_1
  · exact leaf4_0_0_0_4_1_1
  · exact leaf4_0_0_0_4_1_2

-- Residual total budget 6; residual column budgets [0, 0, 4, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_4_2 : suffix4 0 0 0 4 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [1, 1, 6, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_5_0 : suffix4 0 0 0 5 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_5_0_0_0
    · exact leaf4_0_0_0_5_0_0_1
  · exact leaf4_0_0_0_5_0_1

-- Residual total budget 6; residual column budgets [0, 0, 5, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_5_1 : suffix4 0 0 0 5 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [0, 0, 6, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_6_0 : suffix4 0 0 0 6 0 = true := by
  decide +kernel

-- Residual total budget 11; residual column budgets [5, 6, 5, 5].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_1_0_0 : suffix4 0 0 1 0 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · apply allLe_intro
          intro r5 hr5
          norm_num at hr5
          interval_cases r5
          · exact leaf4_0_0_1_0_0_0_0_0_0_0
          · exact leaf4_0_0_1_0_0_0_0_0_0_1
          · exact leaf4_0_0_1_0_0_0_0_0_0_2
          · exact leaf4_0_0_1_0_0_0_0_0_0_3
          · exact leaf4_0_0_1_0_0_0_0_0_0_4
          · exact leaf4_0_0_1_0_0_0_0_0_0_5
        · exact leaf4_0_0_1_0_0_0_0_0_1
        · exact leaf4_0_0_1_0_0_0_0_0_2
        · exact leaf4_0_0_1_0_0_0_0_0_3
        · exact leaf4_0_0_1_0_0_0_0_0_4
        · exact leaf4_0_0_1_0_0_0_0_0_5
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_0_0_1_0
        · exact leaf4_0_0_1_0_0_0_0_1_1
        · exact leaf4_0_0_1_0_0_0_0_1_2
        · exact leaf4_0_0_1_0_0_0_0_1_3
        · exact leaf4_0_0_1_0_0_0_0_1_4
        · exact leaf4_0_0_1_0_0_0_0_1_5
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_0_0_2_0
        · exact leaf4_0_0_1_0_0_0_0_2_1
        · exact leaf4_0_0_1_0_0_0_0_2_2
        · exact leaf4_0_0_1_0_0_0_0_2_3
        · exact leaf4_0_0_1_0_0_0_0_2_4
        · exact leaf4_0_0_1_0_0_0_0_2_5
      · exact leaf4_0_0_1_0_0_0_0_3
      · exact leaf4_0_0_1_0_0_0_0_4
      · exact leaf4_0_0_1_0_0_0_0_5
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_0_1_0_0
        · exact leaf4_0_0_1_0_0_0_1_0_1
        · exact leaf4_0_0_1_0_0_0_1_0_2
        · exact leaf4_0_0_1_0_0_0_1_0_3
        · exact leaf4_0_0_1_0_0_0_1_0_4
        · exact leaf4_0_0_1_0_0_0_1_0_5
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_0_1_1_0
        · exact leaf4_0_0_1_0_0_0_1_1_1
        · exact leaf4_0_0_1_0_0_0_1_1_2
        · exact leaf4_0_0_1_0_0_0_1_1_3
        · exact leaf4_0_0_1_0_0_0_1_1_4
        · exact leaf4_0_0_1_0_0_0_1_1_5
      · exact leaf4_0_0_1_0_0_0_1_2
      · exact leaf4_0_0_1_0_0_0_1_3
      · exact leaf4_0_0_1_0_0_0_1_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_0_2_0_0
        · exact leaf4_0_0_1_0_0_0_2_0_1
        · exact leaf4_0_0_1_0_0_0_2_0_2
        · exact leaf4_0_0_1_0_0_0_2_0_3
        · exact leaf4_0_0_1_0_0_0_2_0_4
      · exact leaf4_0_0_1_0_0_0_2_1
      · exact leaf4_0_0_1_0_0_0_2_2
      · exact leaf4_0_0_1_0_0_0_2_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_0_0_3_0
      · exact leaf4_0_0_1_0_0_0_3_1
      · exact leaf4_0_0_1_0_0_0_3_2
    · exact leaf4_0_0_1_0_0_0_4
    · exact leaf4_0_0_1_0_0_0_5
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_1_0_0_0
        · exact leaf4_0_0_1_0_0_1_0_0_1
        · exact leaf4_0_0_1_0_0_1_0_0_2
        · exact leaf4_0_0_1_0_0_1_0_0_3
        · exact leaf4_0_0_1_0_0_1_0_0_4
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_1_0_1_0
        · exact leaf4_0_0_1_0_0_1_0_1_1
        · exact leaf4_0_0_1_0_0_1_0_1_2
        · exact leaf4_0_0_1_0_0_1_0_1_3
        · exact leaf4_0_0_1_0_0_1_0_1_4
      · exact leaf4_0_0_1_0_0_1_0_2
      · exact leaf4_0_0_1_0_0_1_0_3
      · exact leaf4_0_0_1_0_0_1_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_1_1_0_0
        · exact leaf4_0_0_1_0_0_1_1_0_1
        · exact leaf4_0_0_1_0_0_1_1_0_2
        · exact leaf4_0_0_1_0_0_1_1_0_3
        · exact leaf4_0_0_1_0_0_1_1_0_4
      · exact leaf4_0_0_1_0_0_1_1_1
      · exact leaf4_0_0_1_0_0_1_1_2
      · exact leaf4_0_0_1_0_0_1_1_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_0_1_2_0
      · exact leaf4_0_0_1_0_0_1_2_1
      · exact leaf4_0_0_1_0_0_1_2_2
    · exact leaf4_0_0_1_0_0_1_3
    · exact leaf4_0_0_1_0_0_1_4
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_0_2_0_0_0
        · exact leaf4_0_0_1_0_0_2_0_0_1
        · exact leaf4_0_0_1_0_0_2_0_0_2
        · exact leaf4_0_0_1_0_0_2_0_0_3
      · exact leaf4_0_0_1_0_0_2_0_1
      · exact leaf4_0_0_1_0_0_2_0_2
      · exact leaf4_0_0_1_0_0_2_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_0_2_1_0
      · exact leaf4_0_0_1_0_0_2_1_1
      · exact leaf4_0_0_1_0_0_2_1_2
    · exact leaf4_0_0_1_0_0_2_2
    · exact leaf4_0_0_1_0_0_2_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_0_3_0_0
      · exact leaf4_0_0_1_0_0_3_0_1
      · exact leaf4_0_0_1_0_0_3_0_2
    · exact leaf4_0_0_1_0_0_3_1
    · exact leaf4_0_0_1_0_0_3_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_1_0_0_4_0
    · exact leaf4_0_0_1_0_0_4_1
  · exact leaf4_0_0_1_0_0_5

-- Residual total budget 10; residual column budgets [4, 5, 4, 5].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_1_0_1 : suffix4 0 0 1 0 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_1_0_0_0_0
        · exact leaf4_0_0_1_0_1_0_0_0_1
        · exact leaf4_0_0_1_0_1_0_0_0_2
        · exact leaf4_0_0_1_0_1_0_0_0_3
        · exact leaf4_0_0_1_0_1_0_0_0_4
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_1_0_0_1_0
        · exact leaf4_0_0_1_0_1_0_0_1_1
        · exact leaf4_0_0_1_0_1_0_0_1_2
        · exact leaf4_0_0_1_0_1_0_0_1_3
        · exact leaf4_0_0_1_0_1_0_0_1_4
      · exact leaf4_0_0_1_0_1_0_0_2
      · exact leaf4_0_0_1_0_1_0_0_3
      · exact leaf4_0_0_1_0_1_0_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_1_0_1_0_0
        · exact leaf4_0_0_1_0_1_0_1_0_1
        · exact leaf4_0_0_1_0_1_0_1_0_2
        · exact leaf4_0_0_1_0_1_0_1_0_3
        · exact leaf4_0_0_1_0_1_0_1_0_4
      · exact leaf4_0_0_1_0_1_0_1_1
      · exact leaf4_0_0_1_0_1_0_1_2
      · exact leaf4_0_0_1_0_1_0_1_3
      · exact leaf4_0_0_1_0_1_0_1_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_1_0_2_0
      · exact leaf4_0_0_1_0_1_0_2_1
      · exact leaf4_0_0_1_0_1_0_2_2
      · exact leaf4_0_0_1_0_1_0_2_3
    · exact leaf4_0_0_1_0_1_0_3
    · exact leaf4_0_0_1_0_1_0_4
    · exact leaf4_0_0_1_0_1_0_5
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_1_0_1_1_0_0_0
        · exact leaf4_0_0_1_0_1_1_0_0_1
        · exact leaf4_0_0_1_0_1_1_0_0_2
        · exact leaf4_0_0_1_0_1_1_0_0_3
      · exact leaf4_0_0_1_0_1_1_0_1
      · exact leaf4_0_0_1_0_1_1_0_2
      · exact leaf4_0_0_1_0_1_1_0_3
      · exact leaf4_0_0_1_0_1_1_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_1_1_1_0
      · exact leaf4_0_0_1_0_1_1_1_1
      · exact leaf4_0_0_1_0_1_1_1_2
      · exact leaf4_0_0_1_0_1_1_1_3
    · exact leaf4_0_0_1_0_1_1_2
    · exact leaf4_0_0_1_0_1_1_3
    · exact leaf4_0_0_1_0_1_1_4
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_1_0_1_2_0_0
      · exact leaf4_0_0_1_0_1_2_0_1
      · exact leaf4_0_0_1_0_1_2_0_2
      · exact leaf4_0_0_1_0_1_2_0_3
    · exact leaf4_0_0_1_0_1_2_1
    · exact leaf4_0_0_1_0_1_2_2
    · exact leaf4_0_0_1_0_1_2_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_1_0_1_3_0
    · exact leaf4_0_0_1_0_1_3_1
    · exact leaf4_0_0_1_0_1_3_2
  · exact leaf4_0_0_1_0_1_4

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_0_0_3_2
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_3_3
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_4_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_4_1
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_4_2
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_5_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_5_1
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_6_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_1_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_1_0_1
