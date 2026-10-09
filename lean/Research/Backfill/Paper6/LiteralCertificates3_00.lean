import Research.Backfill.Paper6.LiteralCounts

/-! Bounded suffix checks; source only, not compiled. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

-- Residual total budget 12; residual column budgets [6, 6, 6].
set_option maxHeartbeats 200000 in
theorem certificate3_0_0 : suffix3 0 0 = true := by
  decide +kernel

-- Residual total budget 11; residual column budgets [6, 5, 5].
set_option maxHeartbeats 200000 in
theorem certificate3_0_1 : suffix3 0 1 = true := by
  decide +kernel

-- Residual total budget 10; residual column budgets [6, 4, 4].
set_option maxHeartbeats 200000 in
theorem certificate3_0_2 : suffix3 0 2 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [6, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate3_0_3 : suffix3 0 3 = true := by
  decide +kernel

-- Residual total budget 8; residual column budgets [6, 2, 2].
set_option maxHeartbeats 200000 in
theorem certificate3_0_4 : suffix3 0 4 = true := by
  decide +kernel

-- Residual total budget 7; residual column budgets [6, 1, 1].
set_option maxHeartbeats 200000 in
theorem certificate3_0_5 : suffix3 0 5 = true := by
  decide +kernel

-- Residual total budget 6; residual column budgets [6, 0, 0].
set_option maxHeartbeats 200000 in
theorem certificate3_0_6 : suffix3 0 6 = true := by
  decide +kernel

-- Residual total budget 11; residual column budgets [5, 5, 5].
set_option maxHeartbeats 200000 in
theorem certificate3_1_0 : suffix3 1 0 = true := by
  decide +kernel

-- Residual total budget 10; residual column budgets [5, 4, 4].
set_option maxHeartbeats 200000 in
theorem certificate3_1_1 : suffix3 1 1 = true := by
  decide +kernel

-- Residual total budget 9; residual column budgets [5, 3, 3].
set_option maxHeartbeats 200000 in
theorem certificate3_1_2 : suffix3 1 2 = true := by
  decide +kernel

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.certificate3_0_0
#print axioms Paper6LiteralLouWang.certificate3_0_1
#print axioms Paper6LiteralLouWang.certificate3_0_2
#print axioms Paper6LiteralLouWang.certificate3_0_3
#print axioms Paper6LiteralLouWang.certificate3_0_4
#print axioms Paper6LiteralLouWang.certificate3_0_5
#print axioms Paper6LiteralLouWang.certificate3_0_6
#print axioms Paper6LiteralLouWang.certificate3_1_0
#print axioms Paper6LiteralLouWang.certificate3_1_1
#print axioms Paper6LiteralLouWang.certificate3_1_2
