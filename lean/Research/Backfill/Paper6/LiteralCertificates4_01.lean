import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_11
import Research.Backfill.Paper6.LiteralLeaves4_12
import Research.Backfill.Paper6.LiteralLeaves4_13
import Research.Backfill.Paper6.LiteralLeaves4_14

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 8; residual column budgets [2, 2, 3, 5].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_1_3 : suffix4 0 0 0 1 3 = true := by
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
      · exact leaf4_0_0_0_1_3_0_0_0
      · exact leaf4_0_0_0_1_3_0_0_1
      · exact leaf4_0_0_0_1_3_0_0_2
    · exact leaf4_0_0_0_1_3_0_1
    · exact leaf4_0_0_0_1_3_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_1_3_1_0
    · exact leaf4_0_0_0_1_3_1_1
    · exact leaf4_0_0_0_1_3_1_2
  · exact leaf4_0_0_0_1_3_2
  · exact leaf4_0_0_0_1_3_3

-- Residual total budget 7; residual column budgets [1, 1, 2, 5].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_1_4 : suffix4 0 0 0 1 4 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_1_4_0_0
    · exact leaf4_0_0_0_1_4_0_1
  · exact leaf4_0_0_0_1_4_1
  · exact leaf4_0_0_0_1_4_2

-- Residual total budget 6; residual column budgets [0, 0, 1, 5].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_1_5 : suffix4 0 0 0 1 5 = true := by
  decide +kernel

-- Residual total budget 10; residual column budgets [4, 4, 6, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_2_0 : suffix4 0 0 0 2 0 = true := by
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
        · exact leaf4_0_0_0_2_0_0_0_0_0
        · exact leaf4_0_0_0_2_0_0_0_0_1
        · exact leaf4_0_0_0_2_0_0_0_0_2
        · exact leaf4_0_0_0_2_0_0_0_0_3
        · exact leaf4_0_0_0_2_0_0_0_0_4
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_0_2_0_0_0_1_0
        · exact leaf4_0_0_0_2_0_0_0_1_1
        · exact leaf4_0_0_0_2_0_0_0_1_2
        · exact leaf4_0_0_0_2_0_0_0_1_3
        · exact leaf4_0_0_0_2_0_0_0_1_4
      · exact leaf4_0_0_0_2_0_0_0_2
      · exact leaf4_0_0_0_2_0_0_0_3
      · exact leaf4_0_0_0_2_0_0_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_0_0_2_0_0_1_0_0
        · exact leaf4_0_0_0_2_0_0_1_0_1
        · exact leaf4_0_0_0_2_0_0_1_0_2
        · exact leaf4_0_0_0_2_0_0_1_0_3
      · exact leaf4_0_0_0_2_0_0_1_1
      · exact leaf4_0_0_0_2_0_0_1_2
      · exact leaf4_0_0_0_2_0_0_1_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_2_0_0_2_0
      · exact leaf4_0_0_0_2_0_0_2_1
      · exact leaf4_0_0_0_2_0_0_2_2
    · exact leaf4_0_0_0_2_0_0_3
    · exact leaf4_0_0_0_2_0_0_4
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
        · exact leaf4_0_0_0_2_0_1_0_0_0
        · exact leaf4_0_0_0_2_0_1_0_0_1
        · exact leaf4_0_0_0_2_0_1_0_0_2
        · exact leaf4_0_0_0_2_0_1_0_0_3
        · exact leaf4_0_0_0_2_0_1_0_0_4
      · exact leaf4_0_0_0_2_0_1_0_1
      · exact leaf4_0_0_0_2_0_1_0_2
      · exact leaf4_0_0_0_2_0_1_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_2_0_1_1_0
      · exact leaf4_0_0_0_2_0_1_1_1
      · exact leaf4_0_0_0_2_0_1_1_2
    · exact leaf4_0_0_0_2_0_1_2
    · exact leaf4_0_0_0_2_0_1_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_2_0_2_0_0
      · exact leaf4_0_0_0_2_0_2_0_1
      · exact leaf4_0_0_0_2_0_2_0_2
    · exact leaf4_0_0_0_2_0_2_1
    · exact leaf4_0_0_0_2_0_2_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_2_0_3_0
    · exact leaf4_0_0_0_2_0_3_1
  · exact leaf4_0_0_0_2_0_4

-- Residual total budget 9; residual column budgets [3, 3, 5, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_2_1 : suffix4 0 0 0 2 1 = true := by
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
        · exact leaf4_0_0_0_2_1_0_0_0_0
        · exact leaf4_0_0_0_2_1_0_0_0_1
        · exact leaf4_0_0_0_2_1_0_0_0_2
        · exact leaf4_0_0_0_2_1_0_0_0_3
      · exact leaf4_0_0_0_2_1_0_0_1
      · exact leaf4_0_0_0_2_1_0_0_2
      · exact leaf4_0_0_0_2_1_0_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_2_1_0_1_0
      · exact leaf4_0_0_0_2_1_0_1_1
      · exact leaf4_0_0_0_2_1_0_1_2
      · exact leaf4_0_0_0_2_1_0_1_3
    · exact leaf4_0_0_0_2_1_0_2
    · exact leaf4_0_0_0_2_1_0_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_2_1_1_0_0
      · exact leaf4_0_0_0_2_1_1_0_1
      · exact leaf4_0_0_0_2_1_1_0_2
      · exact leaf4_0_0_0_2_1_1_0_3
    · exact leaf4_0_0_0_2_1_1_1
    · exact leaf4_0_0_0_2_1_1_2
    · exact leaf4_0_0_0_2_1_1_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_2_1_2_0
    · exact leaf4_0_0_0_2_1_2_1
    · exact leaf4_0_0_0_2_1_2_2
  · exact leaf4_0_0_0_2_1_3
  · exact leaf4_0_0_0_2_1_4

-- Residual total budget 8; residual column budgets [2, 2, 4, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_2_2 : suffix4 0 0 0 2 2 = true := by
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
      · exact leaf4_0_0_0_2_2_0_0_0
      · exact leaf4_0_0_0_2_2_0_0_1
      · exact leaf4_0_0_0_2_2_0_0_2
    · exact leaf4_0_0_0_2_2_0_1
    · exact leaf4_0_0_0_2_2_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_2_2_1_0
    · exact leaf4_0_0_0_2_2_1_1
    · exact leaf4_0_0_0_2_2_1_2
  · exact leaf4_0_0_0_2_2_2
  · exact leaf4_0_0_0_2_2_3
  · exact leaf4_0_0_0_2_2_4

-- Residual total budget 7; residual column budgets [1, 1, 3, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_2_3 : suffix4 0 0 0 2 3 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_2_3_0_0
    · exact leaf4_0_0_0_2_3_0_1
  · exact leaf4_0_0_0_2_3_1
  · exact leaf4_0_0_0_2_3_2
  · exact leaf4_0_0_0_2_3_3

-- Residual total budget 6; residual column budgets [0, 0, 2, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_2_4 : suffix4 0 0 0 2 4 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [3, 3, 6, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_3_0 : suffix4 0 0 0 3 0 = true := by
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
        · exact leaf4_0_0_0_3_0_0_0_0_0
        · exact leaf4_0_0_0_3_0_0_0_0_1
        · exact leaf4_0_0_0_3_0_0_0_0_2
        · exact leaf4_0_0_0_3_0_0_0_0_3
      · exact leaf4_0_0_0_3_0_0_0_1
      · exact leaf4_0_0_0_3_0_0_0_2
      · exact leaf4_0_0_0_3_0_0_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_3_0_0_1_0
      · exact leaf4_0_0_0_3_0_0_1_1
      · exact leaf4_0_0_0_3_0_0_1_2
    · exact leaf4_0_0_0_3_0_0_2
    · exact leaf4_0_0_0_3_0_0_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_0_0_3_0_1_0_0
      · exact leaf4_0_0_0_3_0_1_0_1
      · exact leaf4_0_0_0_3_0_1_0_2
    · exact leaf4_0_0_0_3_0_1_1
    · exact leaf4_0_0_0_3_0_1_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_3_0_2_0
    · exact leaf4_0_0_0_3_0_2_1
  · exact leaf4_0_0_0_3_0_3

-- Residual total budget 8; residual column budgets [2, 2, 5, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_0_0_3_1 : suffix4 0 0 0 3 1 = true := by
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
      · exact leaf4_0_0_0_3_1_0_0_0
      · exact leaf4_0_0_0_3_1_0_0_1
      · exact leaf4_0_0_0_3_1_0_0_2
    · exact leaf4_0_0_0_3_1_0_1
    · exact leaf4_0_0_0_3_1_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_0_0_3_1_1_0
    · exact leaf4_0_0_0_3_1_1_1
    · exact leaf4_0_0_0_3_1_1_2
  · exact leaf4_0_0_0_3_1_2
  · exact leaf4_0_0_0_3_1_3

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_0_0_1_3
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_1_4
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_1_5
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_2_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_2_1
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_2_2
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_2_3
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_2_4
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_3_0
#print axioms Paper6LiteralLouWang.certificate4_0_0_0_3_1
