import Research.Backfill.Paper6.LiteralCounts

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 8; residual column budgets [5, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate3_1_3 : suffix3 1 3 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [5, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_1_4 : suffix3 1 4 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [5, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_1_5 : suffix3 1 5 = true := by
  decide +kernel

-- Residual total budget 10; residual column budgets [4, 4, 4].
set_option maxHeartbeats 200000 in
theorem certificate3_2_0 : suffix3 2 0 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [4, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate3_2_1 : suffix3 2 1 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [4, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate3_2_2 : suffix3 2 2 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [4, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_2_3 : suffix3 2 3 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [4, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_2_4 : suffix3 2 4 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [3, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate3_3_0 : suffix3 3 0 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [3, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate3_3_1 : suffix3 3 1 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate3_1_3
#print axioms Paper6LiteralLouWang.certificate3_1_4
#print axioms Paper6LiteralLouWang.certificate3_1_5
#print axioms Paper6LiteralLouWang.certificate3_2_0
#print axioms Paper6LiteralLouWang.certificate3_2_1
#print axioms Paper6LiteralLouWang.certificate3_2_2
#print axioms Paper6LiteralLouWang.certificate3_2_3
#print axioms Paper6LiteralLouWang.certificate3_2_4
#print axioms Paper6LiteralLouWang.certificate3_3_0
#print axioms Paper6LiteralLouWang.certificate3_3_1
