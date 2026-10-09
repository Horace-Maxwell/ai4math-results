import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_36

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [2, 4, 2, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_3_1_0 : suffix4 0 1 3 1 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_3_1_0_0_0
    · exact leaf4_0_1_3_1_0_0_1
  · exact leaf4_0_1_3_1_0_1

-- Residual total budget 6; residual column budgets [1, 3, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_3_1_1 : suffix4 0 1 3 1 1 = true := by
  decide +kernel

-- Residual total budget 5; residual column budgets [0, 2, 0, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_3_1_2 : suffix4 0 1 3 1 2 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [1, 3, 2, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_3_2_0 : suffix4 0 1 3 2 0 = true := by
  decide +kernel

-- Residual total budget 5; residual column budgets [0, 2, 1, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_3_2_1 : suffix4 0 1 3 2 1 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [2, 5, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_4_0_0 : suffix4 0 1 4 0 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_0_1_4_0_0_0_0
    · exact leaf4_0_1_4_0_0_0_1
  · exact leaf4_0_1_4_0_0_1

-- Residual total budget 6; residual column budgets [1, 4, 0, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_4_0_1 : suffix4 0 1 4 0 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [1, 4, 1, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_4_1_0 : suffix4 0 1 4 1 0 = true := by
  decide +kernel

-- Residual total budget 5; residual column budgets [0, 3, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_4_1_1 : suffix4 0 1 4 1 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [1, 5, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_0_1_5_0_0 : suffix4 0 1 5 0 0 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_0_1_3_1_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_3_1_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_3_1_2
#print axioms Paper6LiteralLouWang.certificate4_0_1_3_2_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_3_2_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_4_0_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_4_0_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_4_1_0
#print axioms Paper6LiteralLouWang.certificate4_0_1_4_1_1
#print axioms Paper6LiteralLouWang.certificate4_0_1_5_0_0
