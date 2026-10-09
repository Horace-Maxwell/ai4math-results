import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_32
import Research.Backfill.Paper6.LiteralLeaves4_33
import Research.Backfill.Paper6.LiteralLeaves4_34

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [2, 1, 4, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_0_3_1 : suffix4 0 1 0 3 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_0_3_1_0_0
    · exact leaf4_0_1_0_3_1_0_1
  · exact leaf4_0_1_0_3_1_1
  · exact leaf4_0_1_0_3_1_2

-- Residual total budget 6; residual column budgets [1, 0, 3, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_0_3_2 : suffix4 0 1 0 3 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [2, 1, 5, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_0_4_0 : suffix4 0 1 0 4 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_0_4_0_0_0
    · exact leaf4_0_1_0_4_0_0_1
  · exact leaf4_0_1_0_4_0_1

-- Residual total budget 6; residual column budgets [1, 0, 4, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_0_4_1 : suffix4 0 1 0 4 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [1, 0, 5, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_0_5_0 : suffix4 0 1 0 5 0 = true := by
  decide +kernel

-- Residual total budget 10; residual column budgets [5, 5, 4, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_1_0_0 : suffix4 0 1 1 0 0 = true := by
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
        · exact leaf4_0_1_1_0_0_0_0_0_0
        · exact leaf4_0_1_1_0_0_0_0_0_1
        · exact leaf4_0_1_1_0_0_0_0_0_2
        · exact leaf4_0_1_1_0_0_0_0_0_3
        · exact leaf4_0_1_1_0_0_0_0_0_4
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_1_1_0_0_0_0_1_0
        · exact leaf4_0_1_1_0_0_0_0_1_1
        · exact leaf4_0_1_1_0_0_0_0_1_2
        · exact leaf4_0_1_1_0_0_0_0_1_3
        · exact leaf4_0_1_1_0_0_0_0_1_4
      · exact leaf4_0_1_1_0_0_0_0_2
      · exact leaf4_0_1_1_0_0_0_0_3
      · exact leaf4_0_1_1_0_0_0_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · apply allLe_intro
        intro r6 hr6
        norm_num at hr6
        interval_cases r6
        · exact leaf4_0_1_1_0_0_0_1_0_0
        · exact leaf4_0_1_1_0_0_0_1_0_1
        · exact leaf4_0_1_1_0_0_0_1_0_2
        · exact leaf4_0_1_1_0_0_0_1_0_3
        · exact leaf4_0_1_1_0_0_0_1_0_4
      · exact leaf4_0_1_1_0_0_0_1_1
      · exact leaf4_0_1_1_0_0_0_1_2
      · exact leaf4_0_1_1_0_0_0_1_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_1_1_0_0_0_2_0
      · exact leaf4_0_1_1_0_0_0_2_1
      · exact leaf4_0_1_1_0_0_0_2_2
    · exact leaf4_0_1_1_0_0_0_3
    · exact leaf4_0_1_1_0_0_0_4
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
        · exact leaf4_0_1_1_0_0_1_0_0_0
        · exact leaf4_0_1_1_0_0_1_0_0_1
        · exact leaf4_0_1_1_0_0_1_0_0_2
        · exact leaf4_0_1_1_0_0_1_0_0_3
      · exact leaf4_0_1_1_0_0_1_0_1
      · exact leaf4_0_1_1_0_0_1_0_2
      · exact leaf4_0_1_1_0_0_1_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_1_1_0_0_1_1_0
      · exact leaf4_0_1_1_0_0_1_1_1
      · exact leaf4_0_1_1_0_0_1_1_2
    · exact leaf4_0_1_1_0_0_1_2
    · exact leaf4_0_1_1_0_0_1_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_1_1_0_0_2_0_0
      · exact leaf4_0_1_1_0_0_2_0_1
      · exact leaf4_0_1_1_0_0_2_0_2
    · exact leaf4_0_1_1_0_0_2_1
    · exact leaf4_0_1_1_0_0_2_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_1_0_0_3_0
    · exact leaf4_0_1_1_0_0_3_1
  · exact leaf4_0_1_1_0_0_4

-- Residual total budget 9; residual column budgets [4, 4, 3, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_1_0_1 : suffix4 0 1 1 0 1 = true := by
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
        · exact leaf4_0_1_1_0_1_0_0_0_0
        · exact leaf4_0_1_1_0_1_0_0_0_1
        · exact leaf4_0_1_1_0_1_0_0_0_2
        · exact leaf4_0_1_1_0_1_0_0_0_3
      · exact leaf4_0_1_1_0_1_0_0_1
      · exact leaf4_0_1_1_0_1_0_0_2
      · exact leaf4_0_1_1_0_1_0_0_3
      · exact leaf4_0_1_1_0_1_0_0_4
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_1_1_0_1_0_1_0
      · exact leaf4_0_1_1_0_1_0_1_1
      · exact leaf4_0_1_1_0_1_0_1_2
      · exact leaf4_0_1_1_0_1_0_1_3
    · exact leaf4_0_1_1_0_1_0_2
    · exact leaf4_0_1_1_0_1_0_3
    · exact leaf4_0_1_1_0_1_0_4
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_1_1_0_1_1_0_0
      · exact leaf4_0_1_1_0_1_1_0_1
      · exact leaf4_0_1_1_0_1_1_0_2
      · exact leaf4_0_1_1_0_1_1_0_3
    · exact leaf4_0_1_1_0_1_1_1
    · exact leaf4_0_1_1_0_1_1_2
    · exact leaf4_0_1_1_0_1_1_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_1_0_1_2_0
    · exact leaf4_0_1_1_0_1_2_1
    · exact leaf4_0_1_1_0_1_2_2
  · exact leaf4_0_1_1_0_1_3

-- Residual total budget 8; residual column budgets [3, 3, 2, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_1_0_2 : suffix4 0 1 1 0 2 = true := by
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
      · exact leaf4_0_1_1_0_2_0_0_0
      · exact leaf4_0_1_1_0_2_0_0_1
      · exact leaf4_0_1_1_0_2_0_0_2
      · exact leaf4_0_1_1_0_2_0_0_3
    · exact leaf4_0_1_1_0_2_0_1
    · exact leaf4_0_1_1_0_2_0_2
    · exact leaf4_0_1_1_0_2_0_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_1_0_2_1_0
    · exact leaf4_0_1_1_0_2_1_1
    · exact leaf4_0_1_1_0_2_1_2
    · exact leaf4_0_1_1_0_2_1_3
  · exact leaf4_0_1_1_0_2_2

-- Residual total budget 7; residual column budgets [2, 2, 1, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_1_0_3 : suffix4 0 1 1 0 3 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_1_0_3_0_0
    · exact leaf4_0_1_1_0_3_0_1
    · exact leaf4_0_1_1_0_3_0_2
  · exact leaf4_0_1_1_0_3_1

-- Residual total budget 6; residual column budgets [1, 1, 0, 4].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_1_0_4 : suffix4 0 1 1 0 4 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_1_0_3_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_0_3_2
#print axioms Paper6LiteralLouWang.certificate4_0_1_0_4_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_0_4_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_0_5_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_1_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_1_0_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_1_0_2
#print axioms Paper6LiteralLouWang.certificate4_0_1_1_0_3
#print axioms Paper6LiteralLouWang.certificate4_0_1_1_0_4
