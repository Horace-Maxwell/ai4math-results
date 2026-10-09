import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_40
import Research.Backfill.Paper6.LiteralLeaves4_41

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 5; residual column budgets [1, 2, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_2_3_1_1 : suffix4 0 2 3 1 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [2, 4, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_2_4_0_0 : suffix4 0 2 4 0 0 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [6, 3, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_0_0 : suffix4 0 3 0 0 0 = true := by
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
        · exact leaf4_0_3_0_0_0_0_0_0_0
        · exact leaf4_0_3_0_0_0_0_0_0_1
        · exact leaf4_0_3_0_0_0_0_0_0_2
        · exact leaf4_0_3_0_0_0_0_0_0_3
      · exact leaf4_0_3_0_0_0_0_0_1
      · exact leaf4_0_3_0_0_0_0_0_2
      · exact leaf4_0_3_0_0_0_0_0_3
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_3_0_0_0_0_1_0
      · exact leaf4_0_3_0_0_0_0_1_1
      · exact leaf4_0_3_0_0_0_0_1_2
    · exact leaf4_0_3_0_0_0_0_2
    · exact leaf4_0_3_0_0_0_0_3
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · apply allLe_intro
      intro r9 hr9
      norm_num at hr9
      interval_cases r9
      · exact leaf4_0_3_0_0_0_1_0_0
      · exact leaf4_0_3_0_0_0_1_0_1
      · exact leaf4_0_3_0_0_0_1_0_2
    · exact leaf4_0_3_0_0_0_1_1
    · exact leaf4_0_3_0_0_0_1_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_0_0_2_0
    · exact leaf4_0_3_0_0_0_2_1
  · exact leaf4_0_3_0_0_0_3

-- Residual total budget 8; residual column budgets [5, 2, 2, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_0_1 : suffix4 0 3 0 0 1 = true := by
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
      · exact leaf4_0_3_0_0_1_0_0_0
      · exact leaf4_0_3_0_0_1_0_0_1
      · exact leaf4_0_3_0_0_1_0_0_2
      · exact leaf4_0_3_0_0_1_0_0_3
    · exact leaf4_0_3_0_0_1_0_1
    · exact leaf4_0_3_0_0_1_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_0_1_1_0
    · exact leaf4_0_3_0_0_1_1_1
    · exact leaf4_0_3_0_0_1_1_2
  · exact leaf4_0_3_0_0_1_2

-- Residual total budget 7; residual column budgets [4, 1, 1, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_0_2 : suffix4 0 3 0 0 2 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_0_2_0_0
    · exact leaf4_0_3_0_0_2_0_1
  · exact leaf4_0_3_0_0_2_1

-- Residual total budget 6; residual column budgets [3, 0, 0, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_0_3 : suffix4 0 3 0 0 3 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [5, 2, 3, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_1_0 : suffix4 0 3 0 1 0 = true := by
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
      · exact leaf4_0_3_0_1_0_0_0_0
      · exact leaf4_0_3_0_1_0_0_0_1
      · exact leaf4_0_3_0_1_0_0_0_2
    · exact leaf4_0_3_0_1_0_0_1
    · exact leaf4_0_3_0_1_0_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_1_0_1_0
    · exact leaf4_0_3_0_1_0_1_1
  · exact leaf4_0_3_0_1_0_2

-- Residual total budget 7; residual column budgets [4, 1, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_1_1 : suffix4 0 3 0 1 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_1_1_0_0
    · exact leaf4_0_3_0_1_1_0_1
  · exact leaf4_0_3_0_1_1_1
  · exact leaf4_0_3_0_1_1_2

-- Residual total budget 6; residual column budgets [3, 0, 1, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_1_2 : suffix4 0 3 0 1 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [4, 1, 3, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_0_2_0 : suffix4 0 3 0 2 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_0_2_0_0_0
    · exact leaf4_0_3_0_2_0_0_1
  · exact leaf4_0_3_0_2_0_1

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_2_3_1_1
#print axioms Paper6LiteralLouWang.certificate4_0_2_4_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_0_1
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_0_2
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_0_3
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_1_0
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_1_1
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_1_2
#print axioms Paper6LiteralLouWang.certificate4_0_3_0_2_0
