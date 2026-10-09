import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_41
import Research.Backfill.Paper6.LiteralLeaves4_42

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [4, 3, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_2_0_0 : suffix4 0 3 2 0 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_3_2_0_0_0_0
    · exact leaf4_0_3_2_0_0_0_1
  · exact leaf4_0_3_2_0_0_1

-- Residual total budget 6; residual column budgets [3, 2, 0, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_2_0_1 : suffix4 0 3 2 0 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [3, 2, 1, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_2_1_0 : suffix4 0 3 2 1 0 = true := by
  decide +kernel

-- Residual total budget 5; residual column budgets [2, 1, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_2_1_1 : suffix4 0 3 2 1 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [3, 3, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_3_3_0_0 : suffix4 0 3 3 0 0 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [6, 2, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_4_0_0_0 : suffix4 0 4 0 0 0 = true := by
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
      · exact leaf4_0_4_0_0_0_0_0_0
      · exact leaf4_0_4_0_0_0_0_0_1
      · exact leaf4_0_4_0_0_0_0_0_2
    · exact leaf4_0_4_0_0_0_0_1
    · exact leaf4_0_4_0_0_0_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_4_0_0_0_1_0
    · exact leaf4_0_4_0_0_0_1_1
  · exact leaf4_0_4_0_0_0_2

-- Residual total budget 7; residual column budgets [5, 1, 1, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_4_0_0_1 : suffix4 0 4 0 0 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_4_0_0_1_0_0
    · exact leaf4_0_4_0_0_1_0_1
  · exact leaf4_0_4_0_0_1_1

-- Residual total budget 6; residual column budgets [4, 0, 0, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_0_4_0_0_2 : suffix4 0 4 0 0 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [5, 1, 2, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_4_0_1_0 : suffix4 0 4 0 1 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_4_0_1_0_0_0
    · exact leaf4_0_4_0_1_0_0_1
  · exact leaf4_0_4_0_1_0_1

-- Residual total budget 6; residual column budgets [4, 0, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_4_0_1_1 : suffix4 0 4 0 1 1 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_3_2_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_3_2_0_1
#print axioms Paper6LiteralLouWang.certificate4_0_3_2_1_0
#print axioms Paper6LiteralLouWang.certificate4_0_3_2_1_1
#print axioms Paper6LiteralLouWang.certificate4_0_3_3_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_4_0_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_4_0_0_1
#print axioms Paper6LiteralLouWang.certificate4_0_4_0_0_2
#print axioms Paper6LiteralLouWang.certificate4_0_4_0_1_0
#print axioms Paper6LiteralLouWang.certificate4_0_4_0_1_1
