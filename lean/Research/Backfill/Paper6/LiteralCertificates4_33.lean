import Research.Backfill.Paper6.LiteralCounts
import Research.Backfill.Paper6.LiteralLeaves4_57
import Research.Backfill.Paper6.LiteralLeaves4_58

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 7; residual column budgets [3, 1, 1, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_0_2 : suffix4 1 2 0 0 2 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_0_0_2_0_0
    · exact leaf4_1_2_0_0_2_0_1
  · exact leaf4_1_2_0_0_2_1

-- Residual total budget 6; residual column budgets [2, 0, 0, 3].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_0_3 : suffix4 1 2 0 0 3 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [4, 2, 3, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_1_0 : suffix4 1 2 0 1 0 = true := by
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
      · exact leaf4_1_2_0_1_0_0_0_0
      · exact leaf4_1_2_0_1_0_0_0_1
      · exact leaf4_1_2_0_1_0_0_0_2
    · exact leaf4_1_2_0_1_0_0_1
    · exact leaf4_1_2_0_1_0_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_0_1_0_1_0
    · exact leaf4_1_2_0_1_0_1_1
  · exact leaf4_1_2_0_1_0_2

-- Residual total budget 7; residual column budgets [3, 1, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_1_1 : suffix4 1 2 0 1 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_0_1_1_0_0
    · exact leaf4_1_2_0_1_1_0_1
  · exact leaf4_1_2_0_1_1_1
  · exact leaf4_1_2_0_1_1_2

-- Residual total budget 6; residual column budgets [2, 0, 1, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_1_2 : suffix4 1 2 0 1 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [3, 1, 3, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_2_0 : suffix4 1 2 0 2 0 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_0_2_0_0_0
    · exact leaf4_1_2_0_2_0_0_1
  · exact leaf4_1_2_0_2_0_1

-- Residual total budget 6; residual column budgets [2, 0, 2, 1].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_2_1 : suffix4 1 2 0 2 1 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [2, 0, 3, 0].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_0_3_0 : suffix4 1 2 0 3 0 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [4, 3, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_1_0_0 : suffix4 1 2 1 0 0 = true := by
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
      · exact leaf4_1_2_1_0_0_0_0_0
      · exact leaf4_1_2_1_0_0_0_0_1
      · exact leaf4_1_2_1_0_0_0_0_2
    · exact leaf4_1_2_1_0_0_0_1
    · exact leaf4_1_2_1_0_0_0_2
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_1_0_0_1_0
    · exact leaf4_1_2_1_0_0_1_1
  · exact leaf4_1_2_1_0_0_2

-- Residual total budget 7; residual column budgets [3, 2, 1, 2].
set_option maxHeartbeats 200000 in
theorem certificate4_1_2_1_0_1 : suffix4 1 2 1 0 1 = true := by
  unfold suffix4
  apply allLe_intro
  intro r12 hr12
  norm_num at hr12
  interval_cases r12
  · apply allLe_intro
    intro r10 hr10
    norm_num at hr10
    interval_cases r10
    · exact leaf4_1_2_1_0_1_0_0
    · exact leaf4_1_2_1_0_1_0_1
    · exact leaf4_1_2_1_0_1_0_2
  · exact leaf4_1_2_1_0_1_1

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate4_1_2_0_0_2
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_0_3
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_1_0
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_1_1
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_1_2
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_2_0
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_2_1
#print axioms Paper6LiteralLouWang.certificate4_1_2_0_3_0
#print axioms Paper6LiteralLouWang.certificate4_1_2_1_0_0
#print axioms Paper6LiteralLouWang.certificate4_1_2_1_0_1
